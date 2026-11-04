/-
Superfusion / GaugeChi / TripleCerts / G6_12

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 6,7,2 6,7,3 6,7,4 6,7,5 6,7,6 6,7,7 \
        --module G6_12 \
        --out Superfusion/GaugeChi/TripleCerts/G6_12.lean

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

Triples (6): (6,7,2), (6,7,3), (6,7,4), (6,7,5), (6,7,6), (6,7,7).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G6_12

open Module

/-! ### The fusion shadows this batch uses (19 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_5_2`, `fuseZ_5_3`, `fuseZ_5_4`, `fuseZ_5_5`, `fuseZ_5_6`, `fuseZ_5_7`, `fuseZ_6_1`, `fuseZ_6_2`, `fuseZ_6_3`, `fuseZ_6_4`, `fuseZ_6_5`, `fuseZ_6_6`, `fuseZ_6_7`, `fuseZ_7_2`, `fuseZ_7_3`, `fuseZ_7_4`, `fuseZ_7_5`, `fuseZ_7_6`, `fuseZ_7_7`. -/

/-! ### The triple `(6,7,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_6_7_2
open Module
theorem hsz6_7_2 : realGauge.gaugeSizeR 6 7 2 = realGauge.gaugeSizeL 6 7 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL6_7_2 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc6_7_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet TL6_7_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T6_7_2 : ((realGauge.D ((6 : ZMod 8) + 7 + 2)).matrixSuper
    (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Tc6_7_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_2 : T6_7_2 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 2)).matrixSuper
    (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 2) Tc6_7_2 0 (by decide)

theorem T6_7_2_ne_zero : T6_7_2 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 2) Tc6_7_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_2_0 : ∀ I J g, Xa6_7_2_0 I J g = Xca6_7_2_0 I J g := by
  decide +kernel

theorem hYtaba6_7_2_0 : ∀ I J g, Ya6_7_2_0 I J g = Yca6_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_2_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xa6_7_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xca6_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ya6_7_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yca6_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_2_0 TL6_7_2 YLa6_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xca6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_2_1 : ∀ I J g, Xa6_7_2_1 I J g = Xca6_7_2_1 I J g := by
  decide +kernel

theorem hYtaba6_7_2_1 : ∀ I J g, Ya6_7_2_1 I J g = Yca6_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta6_7_2_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xa6_7_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_6_1 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xca6_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ya6_7_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yca6_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_2_1 TL6_7_2 YLa6_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xca6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_2_2 : ∀ I J g, Xa6_7_2_2 I J g = Xca6_7_2_2 I J g := by
  decide +kernel

theorem hYtaba6_7_2_2 : ∀ I J g, Ya6_7_2_2 I J g = Yca6_7_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta6_7_2_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xa6_7_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_6_1 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xca6_7_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ya6_7_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yca6_7_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_2_2 TL6_7_2 YLa6_7_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (2 : ZMod 8)).1 (realSize (7 : ZMod 8) (2 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xca6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_2_3 : ∀ I J g, Xa6_7_2_3 I J g = Xca6_7_2_3 I J g := by
  decide +kernel

theorem hYtaba6_7_2_3 : ∀ I J g, Ya6_7_2_3 I J g = Yca6_7_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_2_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xa6_7_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_6_1 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xca6_7_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ya6_7_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yca6_7_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_2_3 TL6_7_2 YLa6_7_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_2_0 : ∀ I J g, Xb6_7_2_0 I J g = Xcb6_7_2_0 I J g := by
  decide +kernel

theorem hYtabb6_7_2_0 : ∀ I J g, Yb6_7_2_0 I J g = Ycb6_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_2_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xb6_7_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcb6_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yb6_7_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycb6_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_2_0 TL6_7_2 YLb6_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_2_1 : ∀ I J g, Xb6_7_2_1 I J g = Xcb6_7_2_1 I J g := by
  decide +kernel

theorem hYtabb6_7_2_1 : ∀ I J g, Yb6_7_2_1 I J g = Ycb6_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb6_7_2_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xb6_7_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcb6_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yb6_7_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_6_7 hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycb6_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_2_1 TL6_7_2 YLb6_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_2_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_2_0 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_2_0 : ∀ I J g, Xc6_7_2_0 I J g = Xcc6_7_2_0 I J g := by
  decide +kernel

theorem hYtabc6_7_2_0 : ∀ I J g, Yc6_7_2_0 I J g = Ycc6_7_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_2_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xc6_7_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcc6_7_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yc6_7_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycc6_7_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_2_0 TL6_7_2 YLc6_7_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_2_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcc6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_2_1 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_2_1 : ∀ I J g, Xc6_7_2_1 I J g = Xcc6_7_2_1 I J g := by
  decide +kernel

theorem hYtabc6_7_2_1 : ∀ I J g, Yc6_7_2_1 I J g = Ycc6_7_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_7_2_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xc6_7_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcc6_7_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yc6_7_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycc6_7_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_2_1 TL6_7_2 YLc6_7_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_7_2_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_2_2 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_2_2 : ∀ I J g, Xc6_7_2_2 I J g = Xcc6_7_2_2 I J g := by
  decide +kernel

theorem hYtabc6_7_2_2 : ∀ I J g, Yc6_7_2_2 I J g = Ycc6_7_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc6_7_2_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xc6_7_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcc6_7_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yc6_7_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycc6_7_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_2_2 TL6_7_2 YLc6_7_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_2 (fuseRow (7 : ZMod 8) (2 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ro (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) ee) (fuseCol (7 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 2) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 I) (ri (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_2 (fuseRow ((6 : ZMod 8) + 7) (2 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_7_2_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_2_3 : (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_2_3 : ∀ I J g, Xc6_7_2_3 I J g = Xcc6_7_2_3 I J g := by
  decide +kernel

theorem hYtabc6_7_2_3 : ∀ I J g, Yc6_7_2_3 I J g = Ycc6_7_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_7_2_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T6_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xc6_7_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hfuseZ_7_2 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Xcc6_7_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Yc6_7_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hfuseZ_5_2 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 2)) Ycc6_7_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 2).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 2).2)) (realRepBasis ((6 : ZMod 8) + 7 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 2) (realGauge.gaugeSizeL 6 7 2).1 (realGauge.gaugeSizeL 6 7 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_2_3 TL6_7_2 YLc6_7_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_2 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_2_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_2 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_2
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_2_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T6_7_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_2 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_7_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_7_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_2_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 T6_7_2 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 hT6_7_2 hAint6_7_2 hBint6_7_2 hCint6_7_2

theorem gtOfT6_7_2_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 T6_7_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) hsz6_7_2 T6_7_2_ne_zero

theorem gInterSpace6_7_2_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_2_mem_gInterSpace, gtOfT6_7_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_2 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (2 : ZMod 8) gInterSpace6_7_2_ne_bot).symm

end Triple_6_7_2

/-! ### The triple `(6,7,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_6_7_3
open Module
theorem hsz6_7_3 : realGauge.gaugeSizeR 6 7 3 = realGauge.gaugeSizeL 6 7 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL6_7_3 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc6_7_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet TL6_7_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T6_7_3 : ((realGauge.D ((6 : ZMod 8) + 7 + 3)).matrixSuper
    (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Tc6_7_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_3 : T6_7_3 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 3)).matrixSuper
    (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 3) Tc6_7_3 0 (by decide)

theorem T6_7_3_ne_zero : T6_7_3 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 3) Tc6_7_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_3_0 : ∀ I J g, Xa6_7_3_0 I J g = Xca6_7_3_0 I J g := by
  decide +kernel

theorem hYtaba6_7_3_0 : ∀ I J g, Ya6_7_3_0 I J g = Yca6_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_3_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xa6_7_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xca6_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ya6_7_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yca6_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_3_0 TL6_7_3 YLa6_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

noncomputable def Xca6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_3_1 : ∀ I J g, Xa6_7_3_1 I J g = Xca6_7_3_1 I J g := by
  decide +kernel

theorem hYtaba6_7_3_1 : ∀ I J g, Ya6_7_3_1 I J g = Yca6_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta6_7_3_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xa6_7_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_6_2 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xca6_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ya6_7_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yca6_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_3_1 TL6_7_3 YLa6_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xca6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_3_2 : ∀ I J g, Xa6_7_3_2 I J g = Xca6_7_3_2 I J g := by
  decide +kernel

theorem hYtaba6_7_3_2 : ∀ I J g, Ya6_7_3_2 I J g = Yca6_7_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta6_7_3_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xa6_7_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_6_2 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xca6_7_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ya6_7_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yca6_7_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_3_2 TL6_7_3 YLa6_7_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (3 : ZMod 8)).1 (realSize (7 : ZMod 8) (3 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xca6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_3_3 : ∀ I J g, Xa6_7_3_3 I J g = Xca6_7_3_3 I J g := by
  decide +kernel

theorem hYtaba6_7_3_3 : ∀ I J g, Ya6_7_3_3 I J g = Yca6_7_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_3_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xa6_7_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_6_2 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xca6_7_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ya6_7_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yca6_7_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_3_3 TL6_7_3 YLa6_7_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_3_0 : ∀ I J g, Xb6_7_3_0 I J g = Xcb6_7_3_0 I J g := by
  decide +kernel

theorem hYtabb6_7_3_0 : ∀ I J g, Yb6_7_3_0 I J g = Ycb6_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_3_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xb6_7_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcb6_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yb6_7_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycb6_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_3_0 TL6_7_3 YLb6_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_3_1 : ∀ I J g, Xb6_7_3_1 I J g = Xcb6_7_3_1 I J g := by
  decide +kernel

theorem hYtabb6_7_3_1 : ∀ I J g, Yb6_7_3_1 I J g = Ycb6_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb6_7_3_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xb6_7_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcb6_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yb6_7_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_6_7 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycb6_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_3_1 TL6_7_3 YLb6_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_0 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_0 : ∀ I J g, Xc6_7_3_0 I J g = Xcc6_7_3_0 I J g := by
  decide +kernel

theorem hYtabc6_7_3_0 : ∀ I J g, Yc6_7_3_0 I J g = Ycc6_7_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_3_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_0 TL6_7_3 YLc6_7_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_1 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_1 : ∀ I J g, Xc6_7_3_1 I J g = Xcc6_7_3_1 I J g := by
  decide +kernel

theorem hYtabc6_7_3_1 : ∀ I J g, Yc6_7_3_1 I J g = Ycc6_7_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_7_3_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_1 TL6_7_3 YLc6_7_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_7_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_7_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

noncomputable def Xcc6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_2 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_2 : ∀ I J g, Xc6_7_3_2 I J g = Xcc6_7_3_2 I J g := by
  decide +kernel

theorem hYtabc6_7_3_2 : ∀ I J g, Yc6_7_3_2 I J g = Ycc6_7_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc6_7_3_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_2 TL6_7_3 YLc6_7_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_7_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_7_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcc6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_3 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_3 : ∀ I J g, Xc6_7_3_3 I J g = Xcc6_7_3_3 I J g := by
  decide +kernel

theorem hYtabc6_7_3_3 : ∀ I J g, Yc6_7_3_3 I J g = Ycc6_7_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_7_3_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_3 TL6_7_3 YLc6_7_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc6_7_3_4 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc6_7_3_4 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc6_7_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc6_7_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc6_7_3_4 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_4 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_4 : ∀ I J g, Xc6_7_3_4 I J g = Xcc6_7_3_4 I J g := by
  decide +kernel

theorem hYtabc6_7_3_4 : ∀ I J g, Yc6_7_3_4 I J g = Ycc6_7_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc6_7_3_4 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_4 TL6_7_3 YLc6_7_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc6_7_3_5 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc6_7_3_5 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc6_7_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc6_7_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcc6_7_3_5 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_5 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_5 : ∀ I J g, Xc6_7_3_5 I J g = Xcc6_7_3_5 I J g := by
  decide +kernel

theorem hYtabc6_7_3_5 : ∀ I J g, Yc6_7_3_5 I J g = Ycc6_7_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc6_7_3_5 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_5 TL6_7_3 YLc6_7_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc6_7_3_6 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc6_7_3_6 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc6_7_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc6_7_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc6_7_3_6 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_6 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_6 : ∀ I J g, Xc6_7_3_6 I J g = Xcc6_7_3_6 I J g := by
  decide +kernel

theorem hYtabc6_7_3_6 : ∀ I J g, Yc6_7_3_6 I J g = Ycc6_7_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc6_7_3_6 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_6 TL6_7_3 YLc6_7_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc6_7_3_7 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_3 (fuseRow (7 : ZMod 8) (3 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ro (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) ee) (fuseCol (7 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 3) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 I) (ri (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc6_7_3_7 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((6 : ZMod 8) + 7) (3 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc6_7_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc6_7_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc6_7_3_7 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_3_7 : (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_3_7 : ∀ I J g, Xc6_7_3_7 I J g = Xcc6_7_3_7 I J g := by
  decide +kernel

theorem hYtabc6_7_3_7 : ∀ I J g, Yc6_7_3_7 I J g = Ycc6_7_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc6_7_3_7 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xc6_7_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hfuseZ_7_3 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Xcc6_7_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Yc6_7_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 3)) Ycc6_7_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 3).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 3).2)) (realRepBasis ((6 : ZMod 8) + 7 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 3) (realGauge.gaugeSizeL 6 7 3).1 (realGauge.gaugeSizeL 6 7 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_3_7 TL6_7_3 YLc6_7_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_3 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_3_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_3 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_3
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_3_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T6_7_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_3 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_7_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_7_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc6_7_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc6_7_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc6_7_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc6_7_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_3_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 T6_7_3 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 hT6_7_3 hAint6_7_3 hBint6_7_3 hCint6_7_3

theorem gtOfT6_7_3_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 T6_7_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) hsz6_7_3 T6_7_3_ne_zero

theorem gInterSpace6_7_3_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_3_mem_gInterSpace, gtOfT6_7_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_3 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (3 : ZMod 8) gInterSpace6_7_3_ne_bot).symm

end Triple_6_7_3

/-! ### The triple `(6,7,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_1 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_6_7_4
open Module
theorem hsz6_7_4 : realGauge.gaugeSizeR 6 7 4 = realGauge.gaugeSizeL 6 7 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL6_7_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, -1], [1, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [-1, 0], [0, 1], [0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc6_7_4 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet TL6_7_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T6_7_4 : ((realGauge.D ((6 : ZMod 8) + 7 + 4)).matrixSuper
    (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Tc6_7_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_4 : T6_7_4 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 4)).matrixSuper
    (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 4) Tc6_7_4 1 (by decide)

theorem T6_7_4_ne_zero : T6_7_4 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 4) Tc6_7_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨1, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_4_0 : ∀ I J g, Xa6_7_4_0 I J g = Xca6_7_4_0 I J g := by
  decide +kernel

theorem hYtaba6_7_4_0 : ∀ I J g, Ya6_7_4_0 I J g = Yca6_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_4_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xa6_7_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xca6_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ya6_7_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yca6_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_4_0 TL6_7_4 YLa6_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, -1], [0, 0]]]

noncomputable def Xca6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_4_1 : ∀ I J g, Xa6_7_4_1 I J g = Xca6_7_4_1 I J g := by
  decide +kernel

theorem hYtaba6_7_4_1 : ∀ I J g, Ya6_7_4_1 I J g = Yca6_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta6_7_4_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xa6_7_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_6_3 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xca6_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ya6_7_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yca6_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_4_1 TL6_7_4 YLa6_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_4_2 : ∀ I J g, Xa6_7_4_2 I J g = Xca6_7_4_2 I J g := by
  decide +kernel

theorem hYtaba6_7_4_2 : ∀ I J g, Ya6_7_4_2 I J g = Yca6_7_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta6_7_4_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xa6_7_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_6_3 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xca6_7_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ya6_7_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yca6_7_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_4_2 TL6_7_4 YLa6_7_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (4 : ZMod 8)).1 (realSize (7 : ZMod 8) (4 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]]]

noncomputable def Xca6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_4_3 : ∀ I J g, Xa6_7_4_3 I J g = Xca6_7_4_3 I J g := by
  decide +kernel

theorem hYtaba6_7_4_3 : ∀ I J g, Ya6_7_4_3 I J g = Yca6_7_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_4_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xa6_7_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_6_3 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xca6_7_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ya6_7_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yca6_7_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_4_3 TL6_7_4 YLa6_7_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_4_0 : ∀ I J g, Xb6_7_4_0 I J g = Xcb6_7_4_0 I J g := by
  decide +kernel

theorem hYtabb6_7_4_0 : ∀ I J g, Yb6_7_4_0 I J g = Ycb6_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_4_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xb6_7_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcb6_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yb6_7_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycb6_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb6_7_4_0 TL6_7_4 YLb6_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, -1], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_4_1 : ∀ I J g, Xb6_7_4_1 I J g = Xcb6_7_4_1 I J g := by
  decide +kernel

theorem hYtabb6_7_4_1 : ∀ I J g, Yb6_7_4_1 I J g = Ycb6_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb6_7_4_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xb6_7_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcb6_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yb6_7_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_6_7 hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycb6_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb6_7_4_1 TL6_7_4 YLb6_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_4_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_4_0 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_4_0 : ∀ I J g, Xc6_7_4_0 I J g = Xcc6_7_4_0 I J g := by
  decide +kernel

theorem hYtabc6_7_4_0 : ∀ I J g, Yc6_7_4_0 I J g = Ycc6_7_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_4_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xc6_7_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcc6_7_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yc6_7_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycc6_7_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_4_0 TL6_7_4 YLc6_7_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcc6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_4_1 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_4_1 : ∀ I J g, Xc6_7_4_1 I J g = Xcc6_7_4_1 I J g := by
  decide +kernel

theorem hYtabc6_7_4_1 : ∀ I J g, Yc6_7_4_1 I J g = Ycc6_7_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_7_4_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xc6_7_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcc6_7_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yc6_7_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycc6_7_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_4_1 TL6_7_4 YLc6_7_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_7_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_7_4_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_4_2 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_4_2 : ∀ I J g, Xc6_7_4_2 I J g = Xcc6_7_4_2 I J g := by
  decide +kernel

theorem hYtabc6_7_4_2 : ∀ I J g, Yc6_7_4_2 I J g = Ycc6_7_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc6_7_4_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xc6_7_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcc6_7_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yc6_7_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycc6_7_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_4_2 TL6_7_4 YLc6_7_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_4 (fuseRow (7 : ZMod 8) (4 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ro (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) ee) (fuseCol (7 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 4) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 I) (ri (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_4 (fuseRow ((6 : ZMod 8) + 7) (4 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_7_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_7_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_4_3 : (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_4_3 : ∀ I J g, Xc6_7_4_3 I J g = Xcc6_7_4_3 I J g := by
  decide +kernel

theorem hYtabc6_7_4_3 : ∀ I J g, Yc6_7_4_3 I J g = Ycc6_7_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_7_4_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T6_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xc6_7_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hfuseZ_7_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Xcc6_7_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Yc6_7_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hfuseZ_5_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 4)) Ycc6_7_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 4).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 4).2)) (realRepBasis ((6 : ZMod 8) + 7 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 4) (realGauge.gaugeSizeL 6 7 4).1 (realGauge.gaugeSizeL 6 7 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_4_3 TL6_7_4 YLc6_7_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_4 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_4_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_4 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_4
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_4_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T6_7_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_4 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_7_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_7_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_4_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 T6_7_4 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 hT6_7_4 hAint6_7_4 hBint6_7_4 hCint6_7_4

theorem gtOfT6_7_4_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 T6_7_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) hsz6_7_4 T6_7_4_ne_zero

theorem gInterSpace6_7_4_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_4_mem_gInterSpace, gtOfT6_7_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_4 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (4 : ZMod 8) gInterSpace6_7_4_ne_bot).symm

end Triple_6_7_4

/-! ### The triple `(6,7,5)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_2 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_6_7_5
open Module
theorem hsz6_7_5 : realGauge.gaugeSizeR 6 7 5 = realGauge.gaugeSizeL 6 7 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL6_7_5 : List (List (List ℤ)) :=
  [[[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc6_7_5 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet TL6_7_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_2`. -/
noncomputable def T6_7_5 : ((realGauge.D ((6 : ZMod 8) + 7 + 5)).matrixSuper
    (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Tc6_7_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_5 : T6_7_5 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 5)).matrixSuper
    (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 5) Tc6_7_5 1 (by decide)

theorem T6_7_5_ne_zero : T6_7_5 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 5) Tc6_7_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨2, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_5_0 : ∀ I J g, Xa6_7_5_0 I J g = Xca6_7_5_0 I J g := by
  decide +kernel

theorem hYtaba6_7_5_0 : ∀ I J g, Ya6_7_5_0 I J g = Yca6_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xa6_7_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xca6_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ya6_7_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yca6_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_5_0 TL6_7_5 YLa6_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_5_1 : ∀ I J g, Xa6_7_5_1 I J g = Xca6_7_5_1 I J g := by
  decide +kernel

theorem hYtaba6_7_5_1 : ∀ I J g, Ya6_7_5_1 I J g = Yca6_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta6_7_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xa6_7_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_6_4 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xca6_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ya6_7_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yca6_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_5_1 TL6_7_5 YLa6_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_5_2 : ∀ I J g, Xa6_7_5_2 I J g = Xca6_7_5_2 I J g := by
  decide +kernel

theorem hYtaba6_7_5_2 : ∀ I J g, Ya6_7_5_2 I J g = Yca6_7_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta6_7_5_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xa6_7_5_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_6_4 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xca6_7_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ya6_7_5_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yca6_7_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_5_2 TL6_7_5 YLa6_7_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (5 : ZMod 8)).1 (realSize (7 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xca6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_5_3 : ∀ I J g, Xa6_7_5_3 I J g = Xca6_7_5_3 I J g := by
  decide +kernel

theorem hYtaba6_7_5_3 : ∀ I J g, Ya6_7_5_3 I J g = Yca6_7_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_5_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xa6_7_5_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_6_4 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xca6_7_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ya6_7_5_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yca6_7_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa6_7_5_3 TL6_7_5 YLa6_7_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_5_0 : ∀ I J g, Xb6_7_5_0 I J g = Xcb6_7_5_0 I J g := by
  decide +kernel

theorem hYtabb6_7_5_0 : ∀ I J g, Yb6_7_5_0 I J g = Ycb6_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xb6_7_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcb6_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yb6_7_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycb6_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb6_7_5_0 TL6_7_5 YLb6_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_5_1 : ∀ I J g, Xb6_7_5_1 I J g = Xcb6_7_5_1 I J g := by
  decide +kernel

theorem hYtabb6_7_5_1 : ∀ I J g, Yb6_7_5_1 I J g = Ycb6_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb6_7_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xb6_7_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcb6_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yb6_7_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_6_7 hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycb6_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb6_7_5_1 TL6_7_5 YLb6_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_0 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_0 : ∀ I J g, Xc6_7_5_0 I J g = Xcc6_7_5_0 I J g := by
  decide +kernel

theorem hYtabc6_7_5_0 : ∀ I J g, Yc6_7_5_0 I J g = Ycc6_7_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_0 TL6_7_5 YLc6_7_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_1 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_1 : ∀ I J g, Xc6_7_5_1 I J g = Xcc6_7_5_1 I J g := by
  decide +kernel

theorem hYtabc6_7_5_1 : ∀ I J g, Yc6_7_5_1 I J g = Ycc6_7_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc6_7_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_1 TL6_7_5 YLc6_7_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_7_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_2 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_2 : ∀ I J g, Xc6_7_5_2 I J g = Xcc6_7_5_2 I J g := by
  decide +kernel

theorem hYtabc6_7_5_2 : ∀ I J g, Yc6_7_5_2 I J g = Ycc6_7_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc6_7_5_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_2 TL6_7_5 YLc6_7_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_7_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_3 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_3 : ∀ I J g, Xc6_7_5_3 I J g = Xcc6_7_5_3 I J g := by
  decide +kernel

theorem hYtabc6_7_5_3 : ∀ I J g, Yc6_7_5_3 I J g = Ycc6_7_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_7_5_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_3 TL6_7_5 YLc6_7_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc6_7_5_4 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc6_7_5_4 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc6_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc6_7_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_4 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_4 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_4 : ∀ I J g, Xc6_7_5_4 I J g = Xcc6_7_5_4 I J g := by
  decide +kernel

theorem hYtabc6_7_5_4 : ∀ I J g, Yc6_7_5_4 I J g = Ycc6_7_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc6_7_5_4 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_4 TL6_7_5 YLc6_7_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc6_7_5_5 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc6_7_5_5 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc6_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc6_7_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_5 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_5 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_5 : ∀ I J g, Xc6_7_5_5 I J g = Xcc6_7_5_5 I J g := by
  decide +kernel

theorem hYtabc6_7_5_5 : ∀ I J g, Yc6_7_5_5 I J g = Ycc6_7_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc6_7_5_5 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_5 TL6_7_5 YLc6_7_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc6_7_5_6 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc6_7_5_6 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc6_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc6_7_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc6_7_5_6 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_6 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_6 : ∀ I J g, Xc6_7_5_6 I J g = Xcc6_7_5_6 I J g := by
  decide +kernel

theorem hYtabc6_7_5_6 : ∀ I J g, Yc6_7_5_6 I J g = Ycc6_7_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc6_7_5_6 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_6 TL6_7_5 YLc6_7_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc6_7_5_7 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_5 (fuseRow (7 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ro (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) ee) (fuseCol (7 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_4 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 5) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 I) (ri (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc6_7_5_7 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_5 (fuseRow ((6 : ZMod 8) + 7) (5 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc6_7_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc6_7_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_5_7 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_5_7 : (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_5_7 : ∀ I J g, Xc6_7_5_7 I J g = Xcc6_7_5_7 I J g := by
  decide +kernel

theorem hYtabc6_7_5_7 : ∀ I J g, Yc6_7_5_7 I J g = Ycc6_7_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc6_7_5_7 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xc6_7_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hfuseZ_7_5 hfuseZ_6_4 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Xcc6_7_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Yc6_7_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hfuseZ_5_5 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 5)) Ycc6_7_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 5).2)) (realRepBasis ((6 : ZMod 8) + 7 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 5) (realGauge.gaugeSizeL 6 7 5).1 (realGauge.gaugeSizeL 6 7 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc6_7_5_7 TL6_7_5 YLc6_7_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_5 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_5_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_5 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_5
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_5_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T6_7_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T6_7_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_7_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_7_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc6_7_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc6_7_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc6_7_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc6_7_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_5_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 T6_7_5 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 hT6_7_5 hAint6_7_5 hBint6_7_5 hCint6_7_5

theorem gtOfT6_7_5_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 T6_7_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) hsz6_7_5 T6_7_5_ne_zero

theorem gInterSpace6_7_5_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_5_mem_gInterSpace, gtOfT6_7_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_5 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (5 : ZMod 8) gInterSpace6_7_5_ne_bot).symm

end Triple_6_7_5

/-! ### The triple `(6,7,6)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_6_7_6
open Module
theorem hsz6_7_6 : realGauge.gaugeSizeR 6 7 6 = realGauge.gaugeSizeL 6 7 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL6_7_6 : List (List (List ℤ)) :=
  [[[1, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 1]],
   [[0, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc6_7_6 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet TL6_7_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T6_7_6 : ((realGauge.D ((6 : ZMod 8) + 7 + 6)).matrixSuper
    (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Tc6_7_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_6 : T6_7_6 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 6)).matrixSuper
    (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 6) Tc6_7_6 0 (by decide)

theorem T6_7_6_ne_zero : T6_7_6 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 6) Tc6_7_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (6 : ZMod 8)).1 (realSize (7 : ZMod 8) (6 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_6_0 : ∀ I J g, Xa6_7_6_0 I J g = Xca6_7_6_0 I J g := by
  decide +kernel

theorem hYtaba6_7_6_0 : ∀ I J g, Ya6_7_6_0 I J g = Yca6_7_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_6_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xa6_7_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xca6_7_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ya6_7_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yca6_7_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_6_0 TL6_7_6 YLa6_7_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (6 : ZMod 8)).1 (realSize (7 : ZMod 8) (6 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_6_1 : ∀ I J g, Xa6_7_6_1 I J g = Xca6_7_6_1 I J g := by
  decide +kernel

theorem hYtaba6_7_6_1 : ∀ I J g, Ya6_7_6_1 I J g = Yca6_7_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta6_7_6_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xa6_7_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_6_5 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xca6_7_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ya6_7_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yca6_7_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_6_1 TL6_7_6 YLa6_7_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (6 : ZMod 8)).1 (realSize (7 : ZMod 8) (6 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_6_2 : ∀ I J g, Xa6_7_6_2 I J g = Xca6_7_6_2 I J g := by
  decide +kernel

theorem hYtaba6_7_6_2 : ∀ I J g, Ya6_7_6_2 I J g = Yca6_7_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta6_7_6_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xa6_7_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_6_5 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xca6_7_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ya6_7_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yca6_7_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_6_2 TL6_7_6 YLa6_7_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (6 : ZMod 8)).1 (realSize (7 : ZMod 8) (6 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xca6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_6_3 : ∀ I J g, Xa6_7_6_3 I J g = Xca6_7_6_3 I J g := by
  decide +kernel

theorem hYtaba6_7_6_3 : ∀ I J g, Ya6_7_6_3 I J g = Yca6_7_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_6_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xa6_7_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_6_5 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xca6_7_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ya6_7_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yca6_7_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_6_3 TL6_7_6 YLa6_7_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_6_0 : ∀ I J g, Xb6_7_6_0 I J g = Xcb6_7_6_0 I J g := by
  decide +kernel

theorem hYtabb6_7_6_0 : ∀ I J g, Yb6_7_6_0 I J g = Ycb6_7_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_6_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xb6_7_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcb6_7_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yb6_7_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycb6_7_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_6_0 TL6_7_6 YLb6_7_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_6_1 : ∀ I J g, Xb6_7_6_1 I J g = Xcb6_7_6_1 I J g := by
  decide +kernel

theorem hYtabb6_7_6_1 : ∀ I J g, Yb6_7_6_1 I J g = Ycb6_7_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb6_7_6_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xb6_7_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcb6_7_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yb6_7_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_6_7 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycb6_7_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_6_1 TL6_7_6 YLb6_7_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_6_0 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_6_0 : ∀ I J g, Xc6_7_6_0 I J g = Xcc6_7_6_0 I J g := by
  decide +kernel

theorem hYtabc6_7_6_0 : ∀ I J g, Yc6_7_6_0 I J g = Ycc6_7_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_6_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xc6_7_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcc6_7_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yc6_7_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycc6_7_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_6_0 TL6_7_6 YLc6_7_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_6_1 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_6_1 : ∀ I J g, Xc6_7_6_1 I J g = Xcc6_7_6_1 I J g := by
  decide +kernel

theorem hYtabc6_7_6_1 : ∀ I J g, Yc6_7_6_1 I J g = Ycc6_7_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_7_6_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xc6_7_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcc6_7_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yc6_7_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycc6_7_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_6_1 TL6_7_6 YLc6_7_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_7_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_7_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcc6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_6_2 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_6_2 : ∀ I J g, Xc6_7_6_2 I J g = Xcc6_7_6_2 I J g := by
  decide +kernel

theorem hYtabc6_7_6_2 : ∀ I J g, Yc6_7_6_2 I J g = Ycc6_7_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc6_7_6_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xc6_7_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcc6_7_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yc6_7_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycc6_7_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_6_2 TL6_7_6 YLc6_7_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_6 (fuseRow (7 : ZMod 8) (6 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ro (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) ee) (fuseCol (7 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_6_5 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 6) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 I) (ri (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((6 : ZMod 8) + 7) (6 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_7_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_7_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_6_3 : (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_6_3 : ∀ I J g, Xc6_7_6_3 I J g = Xcc6_7_6_3 I J g := by
  decide +kernel

theorem hYtabc6_7_6_3 : ∀ I J g, Yc6_7_6_3 I J g = Ycc6_7_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_7_6_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xc6_7_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hfuseZ_7_6 hfuseZ_6_5 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Xcc6_7_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Yc6_7_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 6)) Ycc6_7_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 6).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 6).2)) (realRepBasis ((6 : ZMod 8) + 7 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 6) (realGauge.gaugeSizeL 6 7 6).1 (realGauge.gaugeSizeL 6 7 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_6_3 TL6_7_6 YLc6_7_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_6_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_6 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_6
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_6_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_6 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_7_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_7_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_6_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 T6_7_6 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 hT6_7_6 hAint6_7_6 hBint6_7_6 hCint6_7_6

theorem gtOfT6_7_6_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 T6_7_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) hsz6_7_6 T6_7_6_ne_zero

theorem gInterSpace6_7_6_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_6_mem_gInterSpace, gtOfT6_7_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_6 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (6 : ZMod 8) gInterSpace6_7_6_ne_bot).symm

end Triple_6_7_6

/-! ### The triple `(6,7,7)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_4 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_6_7_7
open Module
theorem hsz6_7_7 : realGauge.gaugeSizeR 6 7 7 = realGauge.gaugeSizeL 6 7 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 4`). -/
def TL6_7_7 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc6_7_7 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet TL6_7_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_4`. -/
noncomputable def T6_7_7 : ((realGauge.D ((6 : ZMod 8) + 7 + 7)).matrixSuper
    (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Tc6_7_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_7_7 : T6_7_7 ∈ ((realGauge.D ((6 : ZMod 8) + 7 + 7)).matrixSuper
    (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 7 + 7) Tc6_7_7 0 (by decide)

theorem T6_7_7_ne_zero : T6_7_7 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 7 + 7) Tc6_7_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (7 : ZMod 8)).1 (realSize (7 : ZMod 8) (7 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_7_0 : ∀ I J g, Xa6_7_7_0 I J g = Xca6_7_7_0 I J g := by
  decide +kernel

theorem hYtaba6_7_7_0 : ∀ I J g, Ya6_7_7_0 I J g = Yca6_7_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_7_7_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xa6_7_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_6_6 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xca6_7_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ya6_7_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yca6_7_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_7_0 TL6_7_7 YLa6_7_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (7 : ZMod 8)).1 (realSize (7 : ZMod 8) (7 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_7_1 : ∀ I J g, Xa6_7_7_1 I J g = Xca6_7_7_1 I J g := by
  decide +kernel

theorem hYtaba6_7_7_1 : ∀ I J g, Ya6_7_7_1 I J g = Yca6_7_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta6_7_7_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xa6_7_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_6_6 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xca6_7_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ya6_7_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yca6_7_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_7_1 TL6_7_7 YLa6_7_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_7_7_2 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (7 : ZMod 8)).1 (realSize (7 : ZMod 8) (7 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_7_7_2 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_7_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_7_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_7_7_2 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_7_2 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_7_2 : ∀ I J g, Xa6_7_7_2 I J g = Xca6_7_7_2 I J g := by
  decide +kernel

theorem hYtaba6_7_7_2 : ∀ I J g, Ya6_7_7_2 I J g = Yca6_7_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta6_7_7_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xa6_7_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_6_6 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xca6_7_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ya6_7_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yca6_7_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_7_2 TL6_7_7 YLa6_7_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_7_7_3 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) = (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) then
      ((sgn (sumParity (realSize (7 : ZMod 8) (7 : ZMod 8)).1 (realSize (7 : ZMod 8) (7 : ZMod 8)).2 (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_7_7_3 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_7_7_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_7_7_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0]]]

noncomputable def Xca6_7_7_3 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa6_7_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_7_7_3 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa6_7_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_7_7_3 : ∀ I J g, Xa6_7_7_3 I J g = Xca6_7_7_3 I J g := by
  decide +kernel

theorem hYtaba6_7_7_3 : ∀ I J g, Ya6_7_7_3 I J g = Yca6_7_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_7_7_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xa6_7_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_6_6 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xca6_7_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_7_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ya6_7_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yca6_7_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_7_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_7_7_3 TL6_7_7 YLa6_7_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_7 (fuseRow (7 : ZMod 8) (7 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) ee) (fuseCol (7 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_7_0 : ∀ I J g, Xb6_7_7_0 I J g = Xcb6_7_7_0 I J g := by
  decide +kernel

theorem hYtabb6_7_7_0 : ∀ I J g, Yb6_7_7_0 I J g = Ycb6_7_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_7_7_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xb6_7_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_7_7 hfuseZ_6_6 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xcb6_7_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yb6_7_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ycb6_7_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_7_0 TL6_7_7 YLb6_7_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_7 (fuseRow (7 : ZMod 8) (7 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) ee) (fuseCol (7 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb6_7_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb6_7_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_7_7_1 : ∀ I J g, Xb6_7_7_1 I J g = Xcb6_7_7_1 I J g := by
  decide +kernel

theorem hYtabb6_7_7_1 : ∀ I J g, Yb6_7_7_1 I J g = Ycb6_7_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb6_7_7_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xb6_7_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_7_7 hfuseZ_6_6 (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xcb6_7_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_7_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yb6_7_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_6_7 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ycb6_7_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_7_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_7_7_1 TL6_7_7 YLb6_7_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_7 (fuseRow (7 : ZMod 8) (7 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) ee) (fuseCol (7 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_7_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_7_0 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_7_0 : ∀ I J g, Xc6_7_7_0 I J g = Xcc6_7_7_0 I J g := by
  decide +kernel

theorem hYtabc6_7_7_0 : ∀ I J g, Yc6_7_7_0 I J g = Ycc6_7_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_7_7_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xc6_7_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_7_7 hfuseZ_6_6 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xcc6_7_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yc6_7_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ycc6_7_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_7_0 TL6_7_7 YLc6_7_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_7_7 (fuseRow (7 : ZMod 8) (7 : ZMod 8) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ro (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) ee) (fuseCol (7 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_6_6 (fuseRow (6 : ZMod 8) ((7 : ZMod 8) + 7) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 I) (ri (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 J) g) (fuseCol (6 : ZMod 8) ((7 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) = (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (lo (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow ((6 : ZMod 8) + 7) (7 : ZMod 8) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) I) (li (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 7) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_7_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xcc6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc6_7_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_7_7_1 : (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2) → Fin (realRepDim ((6 : ZMod 8) + 7 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc6_7_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_7_7_1 : ∀ I J g, Xc6_7_7_1 I J g = Xcc6_7_7_1 I J g := by
  decide +kernel

theorem hYtabc6_7_7_1 : ∀ I J g, Yc6_7_7_1 I J g = Ycc6_7_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_7_7_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xc6_7_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hfuseZ_7_7 hfuseZ_6_6 (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Xcc6_7_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_7_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Yc6_7_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 7 + 7)) Ycc6_7_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 7 7).1 ⊕ Fin (realGauge.gaugeSizeL 6 7 7).2)) (realRepBasis ((6 : ZMod 8) + 7 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_7_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 7 + 7) (realGauge.gaugeSizeL 6 7 7).1 (realGauge.gaugeSizeL 6 7 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_7_7_1 TL6_7_7 YLc6_7_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_7_7 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_7_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_7_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_7_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_7_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_7_7_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_7_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_7_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_7_7_1

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_7_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T6_7_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_7_7 * (realGauge.gaugeRouteL (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_7_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_7_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_7_7_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 T6_7_7 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 hT6_7_7 hAint6_7_7 hBint6_7_7 hCint6_7_7

theorem gtOfT6_7_7_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 T6_7_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) hsz6_7_7 T6_7_7_ne_zero

theorem gInterSpace6_7_7_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_7_7_mem_gInterSpace, gtOfT6_7_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_7_7 : gParity ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (7 : ZMod 8) (7 : ZMod 8) gInterSpace6_7_7_ne_bot).symm

end Triple_6_7_7

end G6_12
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_2
#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_3
#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_4
#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_5
#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_6
#print axioms Superfusion.GaugeChi.TripleCerts.G6_12.gParity_6_7_7
