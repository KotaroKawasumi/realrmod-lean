/-
Superfusion / GaugeChi / TripleCerts / G3_20

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 3,6,2 3,6,4 3,6,6 3,6,7 \
        --module G3_20 \
        --out Superfusion/GaugeChi/TripleCerts/G3_20.lean

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

Triples (4): (3,6,2), (3,6,4), (3,6,6), (3,6,7).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G3_20

open Module

/-! ### The fusion shadows this batch uses (13 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_2`, `fuseZ_1_4`, `fuseZ_1_6`, `fuseZ_1_7`, `fuseZ_3_0`, `fuseZ_3_2`, `fuseZ_3_4`, `fuseZ_3_5`, `fuseZ_3_6`, `fuseZ_6_2`, `fuseZ_6_4`, `fuseZ_6_6`, `fuseZ_6_7`. -/

/-! ### The triple `(3,6,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_3_6_2
open Module
theorem hsz3_6_2 : realGauge.gaugeSizeR 3 6 2 = realGauge.gaugeSizeL 3 6 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, -1, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc3_6_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet TL3_6_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T3_6_2 : ((realGauge.D ((3 : ZMod 8) + 6 + 2)).matrixSuper
    (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Tc3_6_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_6_2 : T3_6_2 ∈ ((realGauge.D ((3 : ZMod 8) + 6 + 2)).matrixSuper
    (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 6 + 2) Tc3_6_2 0 (by decide)

theorem T3_6_2_ne_zero : T3_6_2 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 6 + 2) Tc3_6_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨6, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_0 : ∀ I J g, Xa3_6_2_0 I J g = Xca3_6_2_0 I J g := by
  decide +kernel

theorem hYtaba3_6_2_0 : ∀ I J g, Ya3_6_2_0 I J g = Yca3_6_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_6_2_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_0 TL3_6_2 YLa3_6_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_1 : ∀ I J g, Xa3_6_2_1 I J g = Xca3_6_2_1 I J g := by
  decide +kernel

theorem hYtaba3_6_2_1 : ∀ I J g, Ya3_6_2_1 I J g = Yca3_6_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta3_6_2_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_1 TL3_6_2 YLa3_6_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_2 : ∀ I J g, Xa3_6_2_2 I J g = Xca3_6_2_2 I J g := by
  decide +kernel

theorem hYtaba3_6_2_2 : ∀ I J g, Ya3_6_2_2 I J g = Yca3_6_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta3_6_2_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_2 TL3_6_2 YLa3_6_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_3 : ∀ I J g, Xa3_6_2_3 I J g = Xca3_6_2_3 I J g := by
  decide +kernel

theorem hYtaba3_6_2_3 : ∀ I J g, Ya3_6_2_3 I J g = Yca3_6_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_6_2_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_3 TL3_6_2 YLa3_6_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_6_2_4 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_6_2_4 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_6_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_6_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_4 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_4 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_4 : ∀ I J g, Xa3_6_2_4 I J g = Xca3_6_2_4 I J g := by
  decide +kernel

theorem hYtaba3_6_2_4 : ∀ I J g, Ya3_6_2_4 I J g = Yca3_6_2_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta3_6_2_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_4 TL3_6_2 YLa3_6_2_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_6_2_5 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_6_2_5 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_6_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_6_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_5 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_5 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_5 : ∀ I J g, Xa3_6_2_5 I J g = Xca3_6_2_5 I J g := by
  decide +kernel

theorem hYtaba3_6_2_5 : ∀ I J g, Ya3_6_2_5 I J g = Yca3_6_2_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_6_2_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_5 TL3_6_2 YLa3_6_2_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_6_2_6 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_6_2_6 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_6_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_6_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_6 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_6 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_6 : ∀ I J g, Xa3_6_2_6 I J g = Xca3_6_2_6 I J g := by
  decide +kernel

theorem hYtaba3_6_2_6 : ∀ I J g, Ya3_6_2_6 I J g = Yca3_6_2_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_6_2_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_6 TL3_6_2 YLa3_6_2_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_6_2_7 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (2 : ZMod 8)).1 (realSize (6 : ZMod 8) (2 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_6_2_7 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_6_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_6_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_2_7 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_2_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_2_7 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_2_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_2_7 : ∀ I J g, Xa3_6_2_7 I J g = Xca3_6_2_7 I J g := by
  decide +kernel

theorem hYtaba3_6_2_7 : ∀ I J g, Ya3_6_2_7 I J g = Yca3_6_2_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta3_6_2_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xa3_6_2_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_3_0 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xca3_6_2_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_2_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ya3_6_2_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yca3_6_2_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_2_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_2_7 TL3_6_2 YLa3_6_2_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_2_0 : ∀ I J g, Xb3_6_2_0 I J g = Xcb3_6_2_0 I J g := by
  decide +kernel

theorem hYtabb3_6_2_0 : ∀ I J g, Yb3_6_2_0 I J g = Ycb3_6_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_6_2_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xb3_6_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcb3_6_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yb3_6_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycb3_6_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_2_0 TL3_6_2 YLb3_6_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_2_1 : ∀ I J g, Xb3_6_2_1 I J g = Xcb3_6_2_1 I J g := by
  decide +kernel

theorem hYtabb3_6_2_1 : ∀ I J g, Yb3_6_2_1 I J g = Ycb3_6_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb3_6_2_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xb3_6_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcb3_6_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yb3_6_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycb3_6_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_2_1 TL3_6_2 YLb3_6_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_2_2 : ∀ I J g, Xb3_6_2_2 I J g = Xcb3_6_2_2 I J g := by
  decide +kernel

theorem hYtabb3_6_2_2 : ∀ I J g, Yb3_6_2_2 I J g = Ycb3_6_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb3_6_2_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xb3_6_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcb3_6_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yb3_6_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycb3_6_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_2_2 TL3_6_2 YLb3_6_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_2_3 : ∀ I J g, Xb3_6_2_3 I J g = Xcb3_6_2_3 I J g := by
  decide +kernel

theorem hYtabb3_6_2_3 : ∀ I J g, Yb3_6_2_3 I J g = Ycb3_6_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_6_2_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xb3_6_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcb3_6_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yb3_6_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_3_6 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycb3_6_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_2_3 TL3_6_2 YLb3_6_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_6_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_2_0 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_2_0 : ∀ I J g, Xc3_6_2_0 I J g = Xcc3_6_2_0 I J g := by
  decide +kernel

theorem hYtabc3_6_2_0 : ∀ I J g, Yc3_6_2_0 I J g = Ycc3_6_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_6_2_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xc3_6_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcc3_6_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yc3_6_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycc3_6_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_2_0 TL3_6_2 YLc3_6_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_6_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

noncomputable def Xcc3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_2_1 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_2_1 : ∀ I J g, Xc3_6_2_1 I J g = Xcc3_6_2_1 I J g := by
  decide +kernel

theorem hYtabc3_6_2_1 : ∀ I J g, Yc3_6_2_1 I J g = Ycc3_6_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc3_6_2_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xc3_6_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcc3_6_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yc3_6_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycc3_6_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_2_1 TL3_6_2 YLc3_6_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_6_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

noncomputable def Xcc3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_2_2 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_2_2 : ∀ I J g, Xc3_6_2_2 I J g = Xcc3_6_2_2 I J g := by
  decide +kernel

theorem hYtabc3_6_2_2 : ∀ I J g, Yc3_6_2_2 I J g = Ycc3_6_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc3_6_2_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xc3_6_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcc3_6_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yc3_6_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycc3_6_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_2_2 TL3_6_2 YLc3_6_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_2 (fuseRow (6 : ZMod 8) (2 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ro (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) ee) (fuseCol (6 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_3_0 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 2) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 I) (ri (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((3 : ZMod 8) + 6) (2 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_6_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_2_3 : (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_2_3 : ∀ I J g, Xc3_6_2_3 I J g = Xcc3_6_2_3 I J g := by
  decide +kernel

theorem hYtabc3_6_2_3 : ∀ I J g, Yc3_6_2_3 I J g = Ycc3_6_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_6_2_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_6_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xc3_6_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hfuseZ_6_2 hfuseZ_3_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Xcc3_6_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Yc3_6_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 2)) Ycc3_6_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 2).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 2).2)) (realRepBasis ((3 : ZMod 8) + 6 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 2) (realGauge.gaugeSizeL 3 6 2).1 (realGauge.gaugeSizeL 3 6 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_2_3 TL3_6_2 YLc3_6_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_6_2 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_6_2
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_6_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_6_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_6_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_6_2_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_6_2_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_6_2_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_6_2_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_6_2_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_6_2 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_6_2
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_6_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_6_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_6_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_6_2_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_6_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T3_6_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_2 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_6_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_6_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_6_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_6_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_6_2_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 T3_6_2 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 hT3_6_2 hAint3_6_2 hBint3_6_2 hCint3_6_2

theorem gtOfT3_6_2_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 T3_6_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) hsz3_6_2 T3_6_2_ne_zero

theorem gInterSpace3_6_2_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_6_2_mem_gInterSpace, gtOfT3_6_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_6_2 : gParity ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (2 : ZMod 8) gInterSpace3_6_2_ne_bot).symm

end Triple_3_6_2

/-! ### The triple `(3,6,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_5 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_3_6_4
open Module
theorem hsz3_6_4 : realGauge.gaugeSizeR 3 6 4 = realGauge.gaugeSizeL 3 6 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL3_6_4 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc3_6_4 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet TL3_6_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T3_6_4 : ((realGauge.D ((3 : ZMod 8) + 6 + 4)).matrixSuper
    (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Tc3_6_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_6_4 : T3_6_4 ∈ ((realGauge.D ((3 : ZMod 8) + 6 + 4)).matrixSuper
    (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 6 + 4) Tc3_6_4 0 (by decide)

theorem T3_6_4_ne_zero : T3_6_4 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 6 + 4) Tc3_6_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_0 : ∀ I J g, Xa3_6_4_0 I J g = Xca3_6_4_0 I J g := by
  decide +kernel

theorem hYtaba3_6_4_0 : ∀ I J g, Ya3_6_4_0 I J g = Yca3_6_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_6_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_0 TL3_6_4 YLa3_6_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xca3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_1 : ∀ I J g, Xa3_6_4_1 I J g = Xca3_6_4_1 I J g := by
  decide +kernel

theorem hYtaba3_6_4_1 : ∀ I J g, Ya3_6_4_1 I J g = Yca3_6_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta3_6_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_1 TL3_6_4 YLa3_6_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_2 : ∀ I J g, Xa3_6_4_2 I J g = Xca3_6_4_2 I J g := by
  decide +kernel

theorem hYtaba3_6_4_2 : ∀ I J g, Ya3_6_4_2 I J g = Yca3_6_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta3_6_4_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_2 TL3_6_4 YLa3_6_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_3 : ∀ I J g, Xa3_6_4_3 I J g = Xca3_6_4_3 I J g := by
  decide +kernel

theorem hYtaba3_6_4_3 : ∀ I J g, Ya3_6_4_3 I J g = Yca3_6_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_6_4_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_3 TL3_6_4 YLa3_6_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_6_4_4 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_6_4_4 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_6_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_6_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_4 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_4 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_4 : ∀ I J g, Xa3_6_4_4 I J g = Xca3_6_4_4 I J g := by
  decide +kernel

theorem hYtaba3_6_4_4 : ∀ I J g, Ya3_6_4_4 I J g = Yca3_6_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta3_6_4_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_4 TL3_6_4 YLa3_6_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_6_4_5 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_6_4_5 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_6_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_6_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_5 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_5 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_5 : ∀ I J g, Xa3_6_4_5 I J g = Xca3_6_4_5 I J g := by
  decide +kernel

theorem hYtaba3_6_4_5 : ∀ I J g, Ya3_6_4_5 I J g = Yca3_6_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_6_4_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_5 TL3_6_4 YLa3_6_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_6_4_6 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_6_4_6 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_6_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_6_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_6 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_6 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_6 : ∀ I J g, Xa3_6_4_6 I J g = Xca3_6_4_6 I J g := by
  decide +kernel

theorem hYtaba3_6_4_6 : ∀ I J g, Ya3_6_4_6 I J g = Yca3_6_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_6_4_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_6 TL3_6_4 YLa3_6_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_6_4_7 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (4 : ZMod 8)).1 (realSize (6 : ZMod 8) (4 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_6_4_7 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_6_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_6_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca3_6_4_7 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_4_7 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_4_7 : ∀ I J g, Xa3_6_4_7 I J g = Xca3_6_4_7 I J g := by
  decide +kernel

theorem hYtaba3_6_4_7 : ∀ I J g, Ya3_6_4_7 I J g = Yca3_6_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta3_6_4_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xa3_6_4_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_3_2 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xca3_6_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ya3_6_4_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yca3_6_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_4_7 TL3_6_4 YLa3_6_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_4_0 : ∀ I J g, Xb3_6_4_0 I J g = Xcb3_6_4_0 I J g := by
  decide +kernel

theorem hYtabb3_6_4_0 : ∀ I J g, Yb3_6_4_0 I J g = Ycb3_6_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_6_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xb3_6_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcb3_6_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yb3_6_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycb3_6_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_4_0 TL3_6_4 YLb3_6_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_4_1 : ∀ I J g, Xb3_6_4_1 I J g = Xcb3_6_4_1 I J g := by
  decide +kernel

theorem hYtabb3_6_4_1 : ∀ I J g, Yb3_6_4_1 I J g = Ycb3_6_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb3_6_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xb3_6_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcb3_6_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yb3_6_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycb3_6_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_4_1 TL3_6_4 YLb3_6_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_4_2 : ∀ I J g, Xb3_6_4_2 I J g = Xcb3_6_4_2 I J g := by
  decide +kernel

theorem hYtabb3_6_4_2 : ∀ I J g, Yb3_6_4_2 I J g = Ycb3_6_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb3_6_4_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xb3_6_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcb3_6_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yb3_6_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycb3_6_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_4_2 TL3_6_4 YLb3_6_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_4_3 : ∀ I J g, Xb3_6_4_3 I J g = Xcb3_6_4_3 I J g := by
  decide +kernel

theorem hYtabb3_6_4_3 : ∀ I J g, Yb3_6_4_3 I J g = Ycb3_6_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_6_4_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xb3_6_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcb3_6_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yb3_6_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_3_6 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycb3_6_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_4_3 TL3_6_4 YLb3_6_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_6_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_4_0 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_4_0 : ∀ I J g, Xc3_6_4_0 I J g = Xcc3_6_4_0 I J g := by
  decide +kernel

theorem hYtabc3_6_4_0 : ∀ I J g, Yc3_6_4_0 I J g = Ycc3_6_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_6_4_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xc3_6_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcc3_6_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yc3_6_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycc3_6_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_4_0 TL3_6_4 YLc3_6_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_6_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcc3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_4_1 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_4_1 : ∀ I J g, Xc3_6_4_1 I J g = Xcc3_6_4_1 I J g := by
  decide +kernel

theorem hYtabc3_6_4_1 : ∀ I J g, Yc3_6_4_1 I J g = Ycc3_6_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc3_6_4_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xc3_6_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcc3_6_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yc3_6_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycc3_6_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_4_1 TL3_6_4 YLc3_6_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_6_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_4_2 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_4_2 : ∀ I J g, Xc3_6_4_2 I J g = Xcc3_6_4_2 I J g := by
  decide +kernel

theorem hYtabc3_6_4_2 : ∀ I J g, Yc3_6_4_2 I J g = Ycc3_6_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc3_6_4_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xc3_6_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcc3_6_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yc3_6_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycc3_6_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_4_2 TL3_6_4 YLc3_6_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_4 (fuseRow (6 : ZMod 8) (4 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ro (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) ee) (fuseCol (6 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_3_2 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 4) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 I) (ri (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((3 : ZMod 8) + 6) (4 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_6_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcc3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_4_3 : (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_4_3 : ∀ I J g, Xc3_6_4_3 I J g = Xcc3_6_4_3 I J g := by
  decide +kernel

theorem hYtabc3_6_4_3 : ∀ I J g, Yc3_6_4_3 I J g = Ycc3_6_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_6_4_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T3_6_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xc3_6_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hfuseZ_6_4 hfuseZ_3_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Xcc3_6_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Yc3_6_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 4)) Ycc3_6_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 4).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 4).2)) (realRepBasis ((3 : ZMod 8) + 6 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 4) (realGauge.gaugeSizeL 3 6 4).1 (realGauge.gaugeSizeL 3 6 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_4_3 TL3_6_4 YLc3_6_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_6_4 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_6_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_6_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_6_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_6_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_6_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_6_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_6_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_6_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_6_4_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_6_4 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_6_4
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_6_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_6_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_6_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_6_4_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_6_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T3_6_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_4 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_6_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_6_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_6_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_6_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_6_4_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 T3_6_4 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 hT3_6_4 hAint3_6_4 hBint3_6_4 hCint3_6_4

theorem gtOfT3_6_4_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 T3_6_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) hsz3_6_4 T3_6_4_ne_zero

theorem gInterSpace3_6_4_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_6_4_mem_gInterSpace, gtOfT3_6_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_6_4 : gParity ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (4 : ZMod 8) gInterSpace3_6_4_ne_bot).symm

end Triple_3_6_4

/-! ### The triple `(3,6,6)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_3_6_6
open Module
theorem hsz3_6_6 : realGauge.gaugeSizeR 3 6 6 = realGauge.gaugeSizeL 3 6 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL3_6_6 : List (List (List ℤ)) :=
  [[[0, 1], [0, -1], [0, -1], [0, -1], [-1, 0], [-1, 0], [1, 0], [-1, 0]],
   [[0, -1], [0, -1], [0, 1], [0, -1], [-1, 0], [1, 0], [1, 0], [1, 0]],
   [[0, 1], [0, -1], [0, 1], [0, 1], [1, 0], [1, 0], [1, 0], [-1, 0]],
   [[0, 1], [0, 1], [0, 1], [0, -1], [-1, 0], [1, 0], [-1, 0], [-1, 0]],
   [[-1, 0], [-1, 0], [-1, 0], [1, 0], [0, -1], [0, 1], [0, -1], [0, -1]],
   [[1, 0], [-1, 0], [1, 0], [1, 0], [0, -1], [0, -1], [0, -1], [0, 1]],
   [[-1, 0], [-1, 0], [1, 0], [-1, 0], [0, 1], [0, -1], [0, -1], [0, -1]],
   [[-1, 0], [1, 0], [1, 0], [1, 0], [0, -1], [0, -1], [0, 1], [0, -1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc3_6_6 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet TL3_6_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T3_6_6 : ((realGauge.D ((3 : ZMod 8) + 6 + 6)).matrixSuper
    (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Tc3_6_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_6_6 : T3_6_6 ∈ ((realGauge.D ((3 : ZMod 8) + 6 + 6)).matrixSuper
    (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 6 + 6) Tc3_6_6 1 (by decide)

theorem T3_6_6_ne_zero : T3_6_6 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 6 + 6) Tc3_6_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_0 : ∀ I J g, Xa3_6_6_0 I J g = Xca3_6_6_0 I J g := by
  decide +kernel

theorem hYtaba3_6_6_0 : ∀ I J g, Ya3_6_6_0 I J g = Yca3_6_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_6_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_0 TL3_6_6 YLa3_6_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_1 : ∀ I J g, Xa3_6_6_1 I J g = Xca3_6_6_1 I J g := by
  decide +kernel

theorem hYtaba3_6_6_1 : ∀ I J g, Ya3_6_6_1 I J g = Yca3_6_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_6_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_1 TL3_6_6 YLa3_6_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_2 : ∀ I J g, Xa3_6_6_2 I J g = Xca3_6_6_2 I J g := by
  decide +kernel

theorem hYtaba3_6_6_2 : ∀ I J g, Ya3_6_6_2 I J g = Yca3_6_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_6_6_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_2 TL3_6_6 YLa3_6_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_3 : ∀ I J g, Xa3_6_6_3 I J g = Xca3_6_6_3 I J g := by
  decide +kernel

theorem hYtaba3_6_6_3 : ∀ I J g, Ya3_6_6_3 I J g = Yca3_6_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_6_6_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_3 TL3_6_6 YLa3_6_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_6_6_4 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_6_6_4 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_6_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_6_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_4 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_4 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_4 : ∀ I J g, Xa3_6_6_4 I J g = Xca3_6_6_4 I J g := by
  decide +kernel

theorem hYtaba3_6_6_4 : ∀ I J g, Ya3_6_6_4 I J g = Yca3_6_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_6_6_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_4 TL3_6_6 YLa3_6_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_6_6_5 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_6_6_5 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_6_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_6_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_5 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_5 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_5 : ∀ I J g, Xa3_6_6_5 I J g = Xca3_6_6_5 I J g := by
  decide +kernel

theorem hYtaba3_6_6_5 : ∀ I J g, Ya3_6_6_5 I J g = Yca3_6_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_6_6_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_5 TL3_6_6 YLa3_6_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_6_6_6 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_6_6_6 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_6_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_6_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xca3_6_6_6 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_6 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_6 : ∀ I J g, Xa3_6_6_6 I J g = Xca3_6_6_6 I J g := by
  decide +kernel

theorem hYtaba3_6_6_6 : ∀ I J g, Ya3_6_6_6 I J g = Yca3_6_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_6_6_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_6 TL3_6_6 YLa3_6_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_6_6_7 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (6 : ZMod 8)).1 (realSize (6 : ZMod 8) (6 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_6_6_7 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_6_6_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_6_6_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca3_6_6_7 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_6_7 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_6_7 : ∀ I J g, Xa3_6_6_7 I J g = Xca3_6_6_7 I J g := by
  decide +kernel

theorem hYtaba3_6_6_7 : ∀ I J g, Ya3_6_6_7 I J g = Yca3_6_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_6_6_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xa3_6_6_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_3_4 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xca3_6_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ya3_6_6_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yca3_6_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_6_6_7 TL3_6_6 YLa3_6_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_6_0 : ∀ I J g, Xb3_6_6_0 I J g = Xcb3_6_6_0 I J g := by
  decide +kernel

theorem hYtabb3_6_6_0 : ∀ I J g, Yb3_6_6_0 I J g = Ycb3_6_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_6_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xb3_6_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcb3_6_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yb3_6_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycb3_6_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_6_6_0 TL3_6_6 YLb3_6_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_6_1 : ∀ I J g, Xb3_6_6_1 I J g = Xcb3_6_6_1 I J g := by
  decide +kernel

theorem hYtabb3_6_6_1 : ∀ I J g, Yb3_6_6_1 I J g = Ycb3_6_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_6_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xb3_6_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcb3_6_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yb3_6_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycb3_6_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_6_6_1 TL3_6_6 YLb3_6_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_6_2 : ∀ I J g, Xb3_6_6_2 I J g = Xcb3_6_6_2 I J g := by
  decide +kernel

theorem hYtabb3_6_6_2 : ∀ I J g, Yb3_6_6_2 I J g = Ycb3_6_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb3_6_6_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xb3_6_6_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcb3_6_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yb3_6_6_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycb3_6_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_6_6_2 TL3_6_6 YLb3_6_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_6_3 : ∀ I J g, Xb3_6_6_3 I J g = Xcb3_6_6_3 I J g := by
  decide +kernel

theorem hYtabb3_6_6_3 : ∀ I J g, Yb3_6_6_3 I J g = Ycb3_6_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_6_6_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xb3_6_6_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcb3_6_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yb3_6_6_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_3_6 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycb3_6_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_6_6_3 TL3_6_6 YLb3_6_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_6_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_6_0 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_6_0 : ∀ I J g, Xc3_6_6_0 I J g = Xcc3_6_6_0 I J g := by
  decide +kernel

theorem hYtabc3_6_6_0 : ∀ I J g, Yc3_6_6_0 I J g = Ycc3_6_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_6_6_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xc3_6_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcc3_6_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yc3_6_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycc3_6_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_6_6_0 TL3_6_6 YLc3_6_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_6_6_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_6_1 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_6_1 : ∀ I J g, Xc3_6_6_1 I J g = Xcc3_6_6_1 I J g := by
  decide +kernel

theorem hYtabc3_6_6_1 : ∀ I J g, Yc3_6_6_1 I J g = Ycc3_6_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc3_6_6_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xc3_6_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcc3_6_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yc3_6_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycc3_6_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_6_6_1 TL3_6_6 YLc3_6_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_6_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_6_2 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_6_2 : ∀ I J g, Xc3_6_6_2 I J g = Xcc3_6_6_2 I J g := by
  decide +kernel

theorem hYtabc3_6_6_2 : ∀ I J g, Yc3_6_6_2 I J g = Ycc3_6_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc3_6_6_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xc3_6_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcc3_6_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yc3_6_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycc3_6_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_6_6_2 TL3_6_6 YLc3_6_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_6 (fuseRow (6 : ZMod 8) (6 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ro (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) ee) (fuseCol (6 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_3_4 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 6) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 I) (ri (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((3 : ZMod 8) + 6) (6 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_6_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_6_3 : (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_6_3 : ∀ I J g, Xc3_6_6_3 I J g = Xcc3_6_6_3 I J g := by
  decide +kernel

theorem hYtabc3_6_6_3 : ∀ I J g, Yc3_6_6_3 I J g = Ycc3_6_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_6_6_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xc3_6_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hfuseZ_6_6 hfuseZ_3_4 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Xcc3_6_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Yc3_6_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 6)) Ycc3_6_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 6).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 6).2)) (realRepBasis ((3 : ZMod 8) + 6 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 6) (realGauge.gaugeSizeL 3 6 6).1 (realGauge.gaugeSizeL 3 6 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_6_6_3 TL3_6_6 YLc3_6_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_6_6 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_6_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_6_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_6_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_6_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_6_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_6_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_6_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_6_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_6_6_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_6_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_6_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_6_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_6_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_6_6_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_6_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_6_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_6_6 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_6_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_6_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_6_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_6_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_6_6_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 T3_6_6 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 hT3_6_6 hAint3_6_6 hBint3_6_6 hCint3_6_6

theorem gtOfT3_6_6_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 T3_6_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) hsz3_6_6 T3_6_6_ne_zero

theorem gInterSpace3_6_6_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_6_6_mem_gInterSpace, gtOfT3_6_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_6_6 : gParity ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (6 : ZMod 8) gInterSpace3_6_6_ne_bot).symm

end Triple_3_6_6

/-! ### The triple `(3,6,7)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `0`; the transported connector literal. -/
section Triple_3_6_7
open Module
theorem hsz3_6_7 : realGauge.gaugeSizeR 3 6 7 = realGauge.gaugeSizeL 3 6 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL3_6_7 : List (List (List ℤ)) :=
  [[[1], [1], [1], [-1], [0], [0], [0], [0]],
   [[-1], [1], [1], [1], [0], [0], [0], [0]],
   [[1], [1], [-1], [1], [0], [0], [0], [0]],
   [[-1], [1], [-1], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [1], [1], [-1]],
   [[0], [0], [0], [0], [-1], [1], [1], [1]],
   [[0], [0], [0], [0], [1], [1], [-1], [1]],
   [[0], [0], [0], [0], [-1], [1], [-1], [-1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc3_6_7 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet TL3_6_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T3_6_7 : ((realGauge.D ((3 : ZMod 8) + 6 + 7)).matrixSuper
    (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Tc3_6_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_6_7 : T3_6_7 ∈ ((realGauge.D ((3 : ZMod 8) + 6 + 7)).matrixSuper
    (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 6 + 7) Tc3_6_7 0 (by decide)

theorem T3_6_7_ne_zero : T3_6_7 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 6 + 7) Tc3_6_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_0 : ∀ I J g, Xa3_6_7_0 I J g = Xca3_6_7_0 I J g := by
  decide +kernel

theorem hYtaba3_6_7_0 : ∀ I J g, Ya3_6_7_0 I J g = Yca3_6_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_6_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_0 TL3_6_7 YLa3_6_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xca3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_1 : ∀ I J g, Xa3_6_7_1 I J g = Xca3_6_7_1 I J g := by
  decide +kernel

theorem hYtaba3_6_7_1 : ∀ I J g, Ya3_6_7_1 I J g = Yca3_6_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta3_6_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_1 TL3_6_7 YLa3_6_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_6_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_6_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_2 : ∀ I J g, Xa3_6_7_2 I J g = Xca3_6_7_2 I J g := by
  decide +kernel

theorem hYtaba3_6_7_2 : ∀ I J g, Ya3_6_7_2 I J g = Yca3_6_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta3_6_7_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_2 TL3_6_7 YLa3_6_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_6_7_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_6_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xca3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_3 : ∀ I J g, Xa3_6_7_3 I J g = Xca3_6_7_3 I J g := by
  decide +kernel

theorem hYtaba3_6_7_3 : ∀ I J g, Ya3_6_7_3 I J g = Yca3_6_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_6_7_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_3 TL3_6_7 YLa3_6_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_6_7_4 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_6_7_4 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_6_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_6_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_6_7_4 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_4 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_4 : ∀ I J g, Xa3_6_7_4 I J g = Xca3_6_7_4 I J g := by
  decide +kernel

theorem hYtaba3_6_7_4 : ∀ I J g, Ya3_6_7_4 I J g = Yca3_6_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `+1`). -/
theorem hinta3_6_7_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_4 TL3_6_7 YLa3_6_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_6_7_5 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_6_7_5 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_6_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_6_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]]]

noncomputable def Xca3_6_7_5 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_5 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_5 : ∀ I J g, Xa3_6_7_5 I J g = Xca3_6_7_5 I J g := by
  decide +kernel

theorem hYtaba3_6_7_5 : ∀ I J g, Ya3_6_7_5 I J g = Yca3_6_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_6_7_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_5 TL3_6_7 YLa3_6_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_6_7_6 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_6_7_6 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_6_7_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_6_7_6 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xca3_6_7_6 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_6 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_6 : ∀ I J g, Xa3_6_7_6 I J g = Xca3_6_7_6 I J g := by
  decide +kernel

theorem hYtaba3_6_7_6 : ∀ I J g, Ya3_6_7_6 I J g = Yca3_6_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_6_7_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_6 TL3_6_7 YLa3_6_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_6_7_7 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) = (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) then
      ((sgn (sumParity (realSize (6 : ZMod 8) (7 : ZMod 8)).1 (realSize (6 : ZMod 8) (7 : ZMod 8)).2 (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_6_7_7 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_6_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_6_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_6_7_7 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa3_6_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_6_7_7 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa3_6_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_6_7_7 : ∀ I J g, Xa3_6_7_7 I J g = Xca3_6_7_7 I J g := by
  decide +kernel

theorem hYtaba3_6_7_7 : ∀ I J g, Ya3_6_7_7 I J g = Yca3_6_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `+1`). -/
theorem hinta3_6_7_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xa3_6_7_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_3_5 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xca3_6_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_6_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ya3_6_7_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yca3_6_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_6_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa3_6_7_7 TL3_6_7 YLa3_6_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_7_0 : ∀ I J g, Xb3_6_7_0 I J g = Xcb3_6_7_0 I J g := by
  decide +kernel

theorem hYtabb3_6_7_0 : ∀ I J g, Yb3_6_7_0 I J g = Ycb3_6_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_6_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xb3_6_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcb3_6_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yb3_6_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycb3_6_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_7_0 TL3_6_7 YLb3_6_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_7_1 : ∀ I J g, Xb3_6_7_1 I J g = Xcb3_6_7_1 I J g := by
  decide +kernel

theorem hYtabb3_6_7_1 : ∀ I J g, Yb3_6_7_1 I J g = Ycb3_6_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb3_6_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xb3_6_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcb3_6_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yb3_6_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycb3_6_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_7_1 TL3_6_7 YLb3_6_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_6_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_6_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_7_2 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_7_2 : ∀ I J g, Xb3_6_7_2 I J g = Xcb3_6_7_2 I J g := by
  decide +kernel

theorem hYtabb3_6_7_2 : ∀ I J g, Yb3_6_7_2 I J g = Ycb3_6_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb3_6_7_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xb3_6_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcb3_6_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yb3_6_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycb3_6_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_7_2 TL3_6_7 YLb3_6_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_6_7_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_6_7_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb3_6_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_6_7_3 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb3_6_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_6_7_3 : ∀ I J g, Xb3_6_7_3 I J g = Xcb3_6_7_3 I J g := by
  decide +kernel

theorem hYtabb3_6_7_3 : ∀ I J g, Yb3_6_7_3 I J g = Ycb3_6_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_6_7_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xb3_6_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcb3_6_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_6_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yb3_6_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_3_6 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycb3_6_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_6_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb3_6_7_3 TL3_6_7 YLb3_6_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_6_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_7_0 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_7_0 : ∀ I J g, Xc3_6_7_0 I J g = Xcc3_6_7_0 I J g := by
  decide +kernel

theorem hYtabc3_6_7_0 : ∀ I J g, Yc3_6_7_0 I J g = Ycc3_6_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_6_7_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xc3_6_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcc3_6_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yc3_6_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycc3_6_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_7_0 TL3_6_7 YLc3_6_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_6_7 (fuseRow (6 : ZMod 8) (7 : ZMod 8) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ro (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) ee) (fuseCol (6 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((6 : ZMod 8) + 7) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 I) (ri (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 J) g) (fuseCol (3 : ZMod 8) ((6 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) = (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (lo (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((3 : ZMod 8) + 6) (7 : ZMod 8) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) I) (li (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 6) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_6_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc3_6_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_6_7_1 : (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2) → Fin (realRepDim ((3 : ZMod 8) + 6 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc3_6_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_6_7_1 : ∀ I J g, Xc3_6_7_1 I J g = Xcc3_6_7_1 I J g := by
  decide +kernel

theorem hYtabc3_6_7_1 : ∀ I J g, Yc3_6_7_1 I J g = Ycc3_6_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc3_6_7_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T3_6_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xc3_6_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hfuseZ_6_7 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Xcc3_6_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_6_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Yc3_6_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 6 + 7)) Ycc3_6_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 6 7).1 ⊕ Fin (realGauge.gaugeSizeL 3 6 7).2)) (realRepBasis ((3 : ZMod 8) + 6 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_6_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 6 + 7) (realGauge.gaugeSizeL 3 6 7).1 (realGauge.gaugeSizeL 3 6 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc3_6_7_1 TL3_6_7 YLc3_6_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_6_7 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_6_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_6_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_6_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_6_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_6_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_6_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_6_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_6_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_6_7_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_6_7 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T3_6_7
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_6_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_6_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_6_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_6_7_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_6_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T3_6_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T3_6_7 * (realGauge.gaugeRouteL (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_6_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_6_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_6_7_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 T3_6_7 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 hT3_6_7 hAint3_6_7 hBint3_6_7 hCint3_6_7

theorem gtOfT3_6_7_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 T3_6_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) hsz3_6_7 T3_6_7_ne_zero

theorem gInterSpace3_6_7_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_6_7_mem_gInterSpace, gtOfT3_6_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_6_7 : gParity ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (6 : ZMod 8) (7 : ZMod 8) gInterSpace3_6_7_ne_bot).symm

end Triple_3_6_7

end G3_20
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G3_20.gParity_3_6_2
#print axioms Superfusion.GaugeChi.TripleCerts.G3_20.gParity_3_6_4
#print axioms Superfusion.GaugeChi.TripleCerts.G3_20.gParity_3_6_6
#print axioms Superfusion.GaugeChi.TripleCerts.G3_20.gParity_3_6_7
