/-
Superfusion / GaugeChi / TripleCerts / G5_12

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 5,6,3 \
        --module G5_12 \
        --out Superfusion/GaugeChi/TripleCerts/G5_12.lean

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

Triples (1): (5,6,3).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G5_12

open Module

/-! ### The fusion shadows this batch uses (4 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_3_3`, `fuseZ_5_1`, `fuseZ_5_6`, `fuseZ_6_3`. -/

/-! ### The triple `(5,6,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_6 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_5_6_3
open Module
theorem hsz5_6_3 : realGauge.gaugeSizeR 5 6 3 = realGauge.gaugeSizeL 5 6 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 4`). -/
def TL5_6_3 : List (List (List ℤ)) :=
  [[[0, 1, -1, 0], [0, 1, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 1], [-1, 0, 0, 1]],
   [[0, -1, -1, 0], [0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 1], [-1, 0, 0, -1]],
   [[0, -1, -1, 0], [0, -1, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 1], [1, 0, 0, 1]],
   [[0, 1, -1, 0], [0, -1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 1], [1, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, -1], [-1, 0, 0, 1], [0, 1, -1, 0], [0, -1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 1], [1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, -1], [1, 0, 0, 1], [0, -1, -1, 0], [0, 1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 1], [-1, 0, 0, 1], [0, -1, 1, 0], [0, -1, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc5_6_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet TL5_6_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T5_6_3 : ((realGauge.D ((5 : ZMod 8) + 6 + 3)).matrixSuper
    (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2).carrier :=
  matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Tc5_6_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT5_6_3 : T5_6_3 ∈ ((realGauge.D ((5 : ZMod 8) + 6 + 3)).matrixSuper
    (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((5 : ZMod 8) + 6 + 3) Tc5_6_3 1 (by decide)

theorem T5_6_3_ne_zero : T5_6_3 ≠ 0 :=
  matOfCoeff_ne_zero ((5 : ZMod 8) + 6 + 3) Tc5_6_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_0 : ∀ I J g, Xa5_6_3_0 I J g = Xca5_6_3_0 I J g := by
  decide +kernel

theorem hYtaba5_6_3_0 : ∀ I J g, Ya5_6_3_0 I J g = Yca5_6_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta5_6_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_0 TL5_6_3 YLa5_6_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_1 : ∀ I J g, Xa5_6_3_1 I J g = Xca5_6_3_1 I J g := by
  decide +kernel

theorem hYtaba5_6_3_1 : ∀ I J g, Ya5_6_3_1 I J g = Yca5_6_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta5_6_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_1 TL5_6_3 YLa5_6_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_2 : ∀ I J g, Xa5_6_3_2 I J g = Xca5_6_3_2 I J g := by
  decide +kernel

theorem hYtaba5_6_3_2 : ∀ I J g, Ya5_6_3_2 I J g = Yca5_6_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta5_6_3_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_2 TL5_6_3 YLa5_6_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xca5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_3 : ∀ I J g, Xa5_6_3_3 I J g = Xca5_6_3_3 I J g := by
  decide +kernel

theorem hYtaba5_6_3_3 : ∀ I J g, Ya5_6_3_3 I J g = Yca5_6_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta5_6_3_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_3 TL5_6_3 YLa5_6_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa5_6_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa5_6_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_4 : ∀ I J g, Xa5_6_3_4 I J g = Xca5_6_3_4 I J g := by
  decide +kernel

theorem hYtaba5_6_3_4 : ∀ I J g, Ya5_6_3_4 I J g = Yca5_6_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta5_6_3_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_4 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_4 TL5_6_3 YLa5_6_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa5_6_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa5_6_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_5 : ∀ I J g, Xa5_6_3_5 I J g = Xca5_6_3_5 I J g := by
  decide +kernel

theorem hYtaba5_6_3_5 : ∀ I J g, Ya5_6_3_5 I J g = Yca5_6_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta5_6_3_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_5 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_5 TL5_6_3 YLa5_6_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa5_6_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa5_6_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_6 : ∀ I J g, Xa5_6_3_6 I J g = Xca5_6_3_6 I J g := by
  decide +kernel

theorem hYtaba5_6_3_6 : ∀ I J g, Ya5_6_3_6 I J g = Yca5_6_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta5_6_3_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_6 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_6 TL5_6_3 YLa5_6_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) = (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (3 : ZMod 8)).1 (realSize (6 : ZMod 8) (3 : ZMod 8)).2 (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa5_6_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa5_6_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa5_6_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa5_6_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba5_6_3_7 : ∀ I J g, Xa5_6_3_7 I J g = Xca5_6_3_7 I J g := by
  decide +kernel

theorem hYtaba5_6_3_7 : ∀ I J g, Ya5_6_3_7 I J g = Yca5_6_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta5_6_3_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xa5_6_3_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_5_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xca5_6_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba5_6_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ya5_6_3_7 := Matrix.ext fun I J => routeL_aSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yca5_6_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba5_6_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa5_6_3_7 TL5_6_3 YLa5_6_3_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_6_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_6_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_6_3_0 : ∀ I J g, Xb5_6_3_0 I J g = Xcb5_6_3_0 I J g := by
  decide +kernel

theorem hYtabb5_6_3_0 : ∀ I J g, Yb5_6_3_0 I J g = Ycb5_6_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb5_6_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xb5_6_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcb5_6_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_6_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yb5_6_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycb5_6_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_6_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_6_3_0 TL5_6_3 YLb5_6_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_6_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_6_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_6_3_1 : ∀ I J g, Xb5_6_3_1 I J g = Xcb5_6_3_1 I J g := by
  decide +kernel

theorem hYtabb5_6_3_1 : ∀ I J g, Yb5_6_3_1 I J g = Ycb5_6_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb5_6_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xb5_6_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcb5_6_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_6_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yb5_6_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycb5_6_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_6_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_6_3_1 TL5_6_3 YLb5_6_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_6_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_6_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_6_3_2 : ∀ I J g, Xb5_6_3_2 I J g = Xcb5_6_3_2 I J g := by
  decide +kernel

theorem hYtabb5_6_3_2 : ∀ I J g, Yb5_6_3_2 I J g = Ycb5_6_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb5_6_3_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xb5_6_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcb5_6_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_6_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yb5_6_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycb5_6_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_6_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_6_3_2 TL5_6_3 YLb5_6_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb5_6_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb5_6_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb5_6_3_3 : ∀ I J g, Xb5_6_3_3 I J g = Xcb5_6_3_3 I J g := by
  decide +kernel

theorem hYtabb5_6_3_3 : ∀ I J g, Yb5_6_3_3 I J g = Ycb5_6_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb5_6_3_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xb5_6_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcb5_6_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb5_6_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yb5_6_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_5_6 hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycb5_6_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb5_6_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb5_6_3_3 TL5_6_3 YLb5_6_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc5_6_3_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_0 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_0 : ∀ I J g, Xc5_6_3_0 I J g = Xcc5_6_3_0 I J g := by
  decide +kernel

theorem hYtabc5_6_3_0 : ∀ I J g, Yc5_6_3_0 I J g = Ycc5_6_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc5_6_3_0 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_0 TL5_6_3 YLc5_6_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc5_6_3_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_1 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_1 : ∀ I J g, Xc5_6_3_1 I J g = Xcc5_6_3_1 I J g := by
  decide +kernel

theorem hYtabc5_6_3_1 : ∀ I J g, Yc5_6_3_1 I J g = Ycc5_6_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc5_6_3_1 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_1 TL5_6_3 YLc5_6_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc5_6_3_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_2 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_2 : ∀ I J g, Xc5_6_3_2 I J g = Xcc5_6_3_2 I J g := by
  decide +kernel

theorem hYtabc5_6_3_2 : ∀ I J g, Yc5_6_3_2 I J g = Ycc5_6_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc5_6_3_2 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_2 TL5_6_3 YLc5_6_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc5_6_3_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_3 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_3 : ∀ I J g, Xc5_6_3_3 I J g = Xcc5_6_3_3 I J g := by
  decide +kernel

theorem hYtabc5_6_3_3 : ∀ I J g, Yc5_6_3_3 I J g = Ycc5_6_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc5_6_3_3 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_3 TL5_6_3 YLc5_6_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc5_6_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc5_6_3_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_4 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_4 : ∀ I J g, Xc5_6_3_4 I J g = Xcc5_6_3_4 I J g := by
  decide +kernel

theorem hYtabc5_6_3_4 : ∀ I J g, Yc5_6_3_4 I J g = Ycc5_6_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc5_6_3_4 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_4 TL5_6_3 YLc5_6_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc5_6_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc5_6_3_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_5 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_5 : ∀ I J g, Xc5_6_3_5 I J g = Xcc5_6_3_5 I J g := by
  decide +kernel

theorem hYtabc5_6_3_5 : ∀ I J g, Yc5_6_3_5 I J g = Ycc5_6_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc5_6_3_5 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_5 TL5_6_3 YLc5_6_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc5_6_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc5_6_3_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcc5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_6 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_6 : ∀ I J g, Xc5_6_3_6 I J g = Xcc5_6_3_6 I J g := by
  decide +kernel

theorem hYtabc5_6_3_6 : ∀ I J g, Yc5_6_3_6 I J g = Ycc5_6_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc5_6_3_6 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_6 TL5_6_3 YLc5_6_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_3 (fuseRow (6 : ZMod 8) (3 : ZMod 8) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ro (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) ee) (fuseCol (6 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow (5 : ZMod 8) ((6 : ZMod 8) + 3) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 I) (ri (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 J) g) (fuseCol (5 : ZMod 8) ((6 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun I J g => if (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) = (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (lo (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_3 (fuseRow ((5 : ZMod 8) + 6) (3 : ZMod 8) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) I) (li (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((5 : ZMod 8) + 6) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc5_6_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc5_6_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc5_6_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc5_6_3_7 : (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2) → Fin (realRepDim ((5 : ZMod 8) + 6 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc5_6_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 4 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc5_6_3_7 : ∀ I J g, Xc5_6_3_7 I J g = Xcc5_6_3_7 I J g := by
  decide +kernel

theorem hYtabc5_6_3_7 : ∀ I J g, Yc5_6_3_7 I J g = Ycc5_6_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc5_6_3_7 :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xc5_6_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hfuseZ_6_3 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Xcc5_6_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc5_6_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Yc5_6_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hfuseZ_3_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((5 : ZMod 8) + 6 + 3)) Ycc5_6_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 5 6 3).1 ⊕ Fin (realGauge.gaugeSizeL 5 6 3).2)) (realRepBasis ((5 : ZMod 8) + 6 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc5_6_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((5 : ZMod 8) + 6 + 3) (realGauge.gaugeSizeL 5 6 3).1 (realGauge.gaugeSizeL 5 6 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc5_6_3_7 TL5_6_3 YLc5_6_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint5_6_3 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T5_6_3
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hinta5_6_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hinta5_6_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hinta5_6_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hinta5_6_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hinta5_6_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hinta5_6_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hinta5_6_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hinta5_6_3_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint5_6_3 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T5_6_3
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb5_6_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb5_6_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb5_6_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb5_6_3_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint5_6_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T5_6_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T5_6_3 * (realGauge.gaugeRouteL (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc5_6_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc5_6_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc5_6_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc5_6_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc5_6_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc5_6_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc5_6_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc5_6_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT5_6_3_mem_gInterSpace :
    gtOfT ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 T5_6_3 ∈ gInterSpace ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 hT5_6_3 hAint5_6_3 hBint5_6_3 hCint5_6_3

theorem gtOfT5_6_3_ne_zero : gtOfT ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 T5_6_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) hsz5_6_3 T5_6_3_ne_zero

theorem gInterSpace5_6_3_ne_bot : gInterSpace ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT5_6_3_mem_gInterSpace, gtOfT5_6_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_5_6_3 : gParity ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (5 : ZMod 8) (6 : ZMod 8) (3 : ZMod 8) gInterSpace5_6_3_ne_bot).symm

end Triple_5_6_3

end G5_12
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G5_12.gParity_5_6_3
