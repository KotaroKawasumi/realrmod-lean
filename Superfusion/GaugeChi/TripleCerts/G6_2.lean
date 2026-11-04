/-
Superfusion / GaugeChi / TripleCerts / G6_2

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 6,3,5 \
        --module G6_2 \
        --out Superfusion/GaugeChi/TripleCerts/G6_2.lean

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

Triples (1): (6,3,5).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G6_2

open Module

/-! ### The fusion shadows this batch uses (4 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_5`, `fuseZ_3_5`, `fuseZ_6_0`, `fuseZ_6_3`. -/

/-! ### The triple `(6,3,5)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_6 = 4`, certgen parity `0`; the transported connector literal. -/
section Triple_6_3_5
open Module
theorem hsz6_3_5 : realGauge.gaugeSizeR 6 3 5 = realGauge.gaugeSizeL 6 3 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 4`). -/
def TL6_3_5 : List (List (List ℤ)) :=
  [[[1, 0, 0, -1], [-1, 0, 0, -1], [-1, 0, 0, -1], [-1, 0, 0, 1], [0, -1, -1, 0], [0, 1, -1, 0], [0, 1, -1, 0], [0, 1, 1, 0]],
   [[1, 0, 0, 1], [1, 0, 0, -1], [1, 0, 0, -1], [-1, 0, 0, -1], [0, 1, -1, 0], [0, 1, 1, 0], [0, 1, 1, 0], [0, -1, 1, 0]],
   [[1, 0, 0, -1], [-1, 0, 0, -1], [1, 0, 0, 1], [1, 0, 0, -1], [0, 1, 1, 0], [0, -1, 1, 0], [0, 1, -1, 0], [0, 1, 1, 0]],
   [[1, 0, 0, 1], [1, 0, 0, -1], [-1, 0, 0, 1], [1, 0, 0, 1], [0, -1, 1, 0], [0, -1, -1, 0], [0, 1, 1, 0], [0, -1, 1, 0]],
   [[0, 1, 1, 0], [0, -1, 1, 0], [0, -1, 1, 0], [0, -1, -1, 0], [1, 0, 0, -1], [-1, 0, 0, -1], [-1, 0, 0, -1], [-1, 0, 0, 1]],
   [[0, -1, 1, 0], [0, -1, -1, 0], [0, -1, -1, 0], [0, 1, -1, 0], [1, 0, 0, 1], [1, 0, 0, -1], [1, 0, 0, -1], [-1, 0, 0, -1]],
   [[0, -1, -1, 0], [0, 1, -1, 0], [0, -1, 1, 0], [0, -1, -1, 0], [1, 0, 0, -1], [-1, 0, 0, -1], [1, 0, 0, 1], [1, 0, 0, -1]],
   [[0, 1, -1, 0], [0, 1, 1, 0], [0, -1, -1, 0], [0, 1, -1, 0], [1, 0, 0, 1], [1, 0, 0, -1], [-1, 0, 0, 1], [1, 0, 0, 1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc6_3_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet TL6_3_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T6_3_5 : ((realGauge.D ((6 : ZMod 8) + 3 + 5)).matrixSuper
    (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2).carrier :=
  matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Tc6_3_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT6_3_5 : T6_3_5 ∈ ((realGauge.D ((6 : ZMod 8) + 3 + 5)).matrixSuper
    (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((6 : ZMod 8) + 3 + 5) Tc6_3_5 0 (by decide)

theorem T6_3_5_ne_zero : T6_3_5 ≠ 0 :=
  matOfCoeff_ne_zero ((6 : ZMod 8) + 3 + 5) Tc6_3_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) = (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_3_5_0 : ∀ I J g, Xa6_3_5_0 I J g = Xca6_3_5_0 I J g := by
  decide +kernel

theorem hYtaba6_3_5_0 : ∀ I J g, Ya6_3_5_0 I J g = Yca6_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta6_3_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xa6_3_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xca6_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ya6_3_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yca6_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_3_5_0 TL6_3_5 YLa6_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) = (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_3_5_1 : ∀ I J g, Xa6_3_5_1 I J g = Xca6_3_5_1 I J g := by
  decide +kernel

theorem hYtaba6_3_5_1 : ∀ I J g, Ya6_3_5_1 I J g = Yca6_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta6_3_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xa6_3_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_6_0 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xca6_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ya6_3_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yca6_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_3_5_1 TL6_3_5 YLa6_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) = (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_3_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_3_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_3_5_2 : ∀ I J g, Xa6_3_5_2 I J g = Xca6_3_5_2 I J g := by
  decide +kernel

theorem hYtaba6_3_5_2 : ∀ I J g, Ya6_3_5_2 I J g = Yca6_3_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta6_3_5_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xa6_3_5_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_6_0 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xca6_3_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_3_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ya6_3_5_2 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yca6_3_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_3_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_3_5_2 TL6_3_5 YLa6_3_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) = (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa6_3_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa6_3_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba6_3_5_3 : ∀ I J g, Xa6_3_5_3 I J g = Xca6_3_5_3 I J g := by
  decide +kernel

theorem hYtaba6_3_5_3 : ∀ I J g, Ya6_3_5_3 I J g = Yca6_3_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta6_3_5_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xa6_3_5_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_6_0 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xca6_3_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba6_3_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ya6_3_5_3 := Matrix.ext fun I J => routeL_aSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yca6_3_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba6_3_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa6_3_5_3 TL6_3_5 YLa6_3_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_0 : ∀ I J g, Xb6_3_5_0 I J g = Xcb6_3_5_0 I J g := by
  decide +kernel

theorem hYtabb6_3_5_0 : ∀ I J g, Yb6_3_5_0 I J g = Ycb6_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb6_3_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_0 TL6_3_5 YLb6_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_1 : ∀ I J g, Xb6_3_5_1 I J g = Xcb6_3_5_1 I J g := by
  decide +kernel

theorem hYtabb6_3_5_1 : ∀ I J g, Yb6_3_5_1 I J g = Ycb6_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb6_3_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_1 TL6_3_5 YLb6_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_2 : ∀ I J g, Xb6_3_5_2 I J g = Xcb6_3_5_2 I J g := by
  decide +kernel

theorem hYtabb6_3_5_2 : ∀ I J g, Yb6_3_5_2 I J g = Ycb6_3_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb6_3_5_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_2 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_2 TL6_3_5 YLb6_3_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_3 : ∀ I J g, Xb6_3_5_3 I J g = Xcb6_3_5_3 I J g := by
  decide +kernel

theorem hYtabb6_3_5_3 : ∀ I J g, Yb6_3_5_3 I J g = Ycb6_3_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb6_3_5_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_3 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_3 TL6_3_5 YLb6_3_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb6_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb6_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_4 : ∀ I J g, Xb6_3_5_4 I J g = Xcb6_3_5_4 I J g := by
  decide +kernel

theorem hYtabb6_3_5_4 : ∀ I J g, Yb6_3_5_4 I J g = Ycb6_3_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb6_3_5_4 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_4 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_4 TL6_3_5 YLb6_3_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb6_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb6_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_5 : ∀ I J g, Xb6_3_5_5 I J g = Xcb6_3_5_5 I J g := by
  decide +kernel

theorem hYtabb6_3_5_5 : ∀ I J g, Yb6_3_5_5 I J g = Ycb6_3_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb6_3_5_5 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_5 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_5 TL6_3_5 YLb6_3_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb6_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb6_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_6 : ∀ I J g, Xb6_3_5_6 I J g = Xcb6_3_5_6 I J g := by
  decide +kernel

theorem hYtabb6_3_5_6 : ∀ I J g, Yb6_3_5_6 I J g = Ycb6_3_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb6_3_5_6 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_6 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_6 TL6_3_5 YLb6_3_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb6_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb6_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb6_3_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb6_3_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb6_3_5_7 : ∀ I J g, Xb6_3_5_7 I J g = Xcb6_3_5_7 I J g := by
  decide +kernel

theorem hYtabb6_3_5_7 : ∀ I J g, Yb6_3_5_7 I J g = Ycb6_3_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb6_3_5_7 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xb6_3_5_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcb6_3_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb6_3_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yb6_3_5_7 := Matrix.ext fun I J => routeL_bSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_6_3 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycb6_3_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb6_3_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb6_3_5_7 TL6_3_5 YLb6_3_5_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc6_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_0 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_0 : ∀ I J g, Xc6_3_5_0 I J g = Xcc6_3_5_0 I J g := by
  decide +kernel

theorem hYtabc6_3_5_0 : ∀ I J g, Yc6_3_5_0 I J g = Ycc6_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc6_3_5_0 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_0 TL6_3_5 YLc6_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc6_3_5_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

noncomputable def Xcc6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_1 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_1 : ∀ I J g, Xc6_3_5_1 I J g = Xcc6_3_5_1 I J g := by
  decide +kernel

theorem hYtabc6_3_5_1 : ∀ I J g, Yc6_3_5_1 I J g = Ycc6_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc6_3_5_1 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_1 TL6_3_5 YLc6_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc6_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

noncomputable def Xcc6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_2 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_2 : ∀ I J g, Xc6_3_5_2 I J g = Xcc6_3_5_2 I J g := by
  decide +kernel

theorem hYtabc6_3_5_2 : ∀ I J g, Yc6_3_5_2 I J g = Ycc6_3_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc6_3_5_2 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_2 TL6_3_5 YLc6_3_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc6_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_3 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_3 : ∀ I J g, Xc6_3_5_3 I J g = Xcc6_3_5_3 I J g := by
  decide +kernel

theorem hYtabc6_3_5_3 : ∀ I J g, Yc6_3_5_3 I J g = Ycc6_3_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc6_3_5_3 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_3 TL6_3_5 YLc6_3_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc6_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc6_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_4 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_4 : ∀ I J g, Xc6_3_5_4 I J g = Xcc6_3_5_4 I J g := by
  decide +kernel

theorem hYtabc6_3_5_4 : ∀ I J g, Yc6_3_5_4 I J g = Ycc6_3_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc6_3_5_4 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_4 TL6_3_5 YLc6_3_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc6_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc6_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_5 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_5 : ∀ I J g, Xc6_3_5_5 I J g = Xcc6_3_5_5 I J g := by
  decide +kernel

theorem hYtabc6_3_5_5 : ∀ I J g, Yc6_3_5_5 I J g = Ycc6_3_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc6_3_5_5 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_5 TL6_3_5 YLc6_3_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc6_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc6_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_6 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_6 : ∀ I J g, Xc6_3_5_6 I J g = Xcc6_3_5_6 I J g := by
  decide +kernel

theorem hYtabc6_3_5_6 : ∀ I J g, Yc6_3_5_6 I J g = Ycc6_3_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc6_3_5_6 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_6 TL6_3_5 YLc6_3_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ro (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow (6 : ZMod 8) ((3 : ZMod 8) + 5) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 I) (ri (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 J) g) (fuseCol (6 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (lo (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow ((6 : ZMod 8) + 3) (5 : ZMod 8) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((6 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc6_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc6_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc6_3_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc6_3_5_7 : (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2) → Fin (realRepDim ((6 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc6_3_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc6_3_5_7 : ∀ I J g, Xc6_3_5_7 I J g = Xcc6_3_5_7 I J g := by
  decide +kernel

theorem hYtabc6_3_5_7 : ∀ I J g, Yc6_3_5_7 I J g = Ycc6_3_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc6_3_5_7 :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xc6_3_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hfuseZ_3_5 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Xcc6_3_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc6_3_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Yc6_3_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((6 : ZMod 8) + 3 + 5)) Ycc6_3_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 6 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 6 3 5).2)) (realRepBasis ((6 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc6_3_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((6 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 6 3 5).1 (realGauge.gaugeSizeL 6 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc6_3_5_7 TL6_3_5 YLc6_3_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint6_3_5 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T6_3_5
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hinta6_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hinta6_3_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hinta6_3_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hinta6_3_5_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint6_3_5 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T6_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb6_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb6_3_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb6_3_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb6_3_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb6_3_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb6_3_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb6_3_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb6_3_5_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint6_3_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T6_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T6_3_5 * (realGauge.gaugeRouteL (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc6_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc6_3_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc6_3_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc6_3_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc6_3_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc6_3_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc6_3_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc6_3_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT6_3_5_mem_gInterSpace :
    gtOfT ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 T6_3_5 ∈ gInterSpace ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 hT6_3_5 hAint6_3_5 hBint6_3_5 hCint6_3_5

theorem gtOfT6_3_5_ne_zero : gtOfT ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 T6_3_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz6_3_5 T6_3_5_ne_zero

theorem gInterSpace6_3_5_ne_bot : gInterSpace ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT6_3_5_mem_gInterSpace, gtOfT6_3_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_6_3_5 : gParity ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (6 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) gInterSpace6_3_5_ne_bot).symm

end Triple_6_3_5

end G6_2
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G6_2.gParity_6_3_5
