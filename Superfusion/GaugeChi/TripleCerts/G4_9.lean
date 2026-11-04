/-
Superfusion / GaugeChi / TripleCerts / G4_9

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 4,5,2 4,5,4 4,5,6 4,5,7 \
        --module G4_9 \
        --out Superfusion/GaugeChi/TripleCerts/G4_9.lean

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

Triples (4): (4,5,2), (4,5,4), (4,5,6), (4,5,7).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G4_9

open Module

/-! ### The fusion shadows this batch uses (13 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_2`, `fuseZ_1_4`, `fuseZ_1_6`, `fuseZ_1_7`, `fuseZ_4_1`, `fuseZ_4_3`, `fuseZ_4_4`, `fuseZ_4_5`, `fuseZ_4_7`, `fuseZ_5_2`, `fuseZ_5_4`, `fuseZ_5_6`, `fuseZ_5_7`. -/

/-! ### The triple `(4,5,2)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `1`; the transported connector literal. -/
section Triple_4_5_2
open Module
theorem hsz4_5_2 : realGauge.gaugeSizeR 4 5 2 = realGauge.gaugeSizeL 4 5 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL4_5_2 : List (List (List ℤ)) :=
  [[[0, 0, -1, 0, -1, 0, 0, 0], [0, 0, -1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, -1, 0], [1, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, -1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 0, 1, 0]],
   [[-1, 0, 0, 0, 0, 0, -1, 0], [-1, 0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 0, -1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0, 0], [0, 0, -1, 0, 1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc4_5_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet TL4_5_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T4_5_2 : ((realGauge.D ((4 : ZMod 8) + 5 + 2)).matrixSuper
    (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Tc4_5_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_5_2 : T4_5_2 ∈ ((realGauge.D ((4 : ZMod 8) + 5 + 2)).matrixSuper
    (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 5 + 2) Tc4_5_2 1 (by decide)

theorem T4_5_2_ne_zero : T4_5_2 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 5 + 2) Tc4_5_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨2, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (2 : ZMod 8)).1 (realSize (5 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_2_0 : ∀ I J g, Xa4_5_2_0 I J g = Xca4_5_2_0 I J g := by
  decide +kernel

theorem hYtaba4_5_2_0 : ∀ I J g, Ya4_5_2_0 I J g = Yca4_5_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_5_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xa4_5_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xca4_5_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ya4_5_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yca4_5_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_2_0 TL4_5_2 YLa4_5_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (2 : ZMod 8)).1 (realSize (5 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_2_1 : ∀ I J g, Xa4_5_2_1 I J g = Xca4_5_2_1 I J g := by
  decide +kernel

theorem hYtaba4_5_2_1 : ∀ I J g, Ya4_5_2_1 I J g = Yca4_5_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_5_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xa4_5_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xca4_5_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ya4_5_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yca4_5_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_2_1 TL4_5_2 YLa4_5_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (2 : ZMod 8)).1 (realSize (5 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_2_2 : ∀ I J g, Xa4_5_2_2 I J g = Xca4_5_2_2 I J g := by
  decide +kernel

theorem hYtaba4_5_2_2 : ∀ I J g, Ya4_5_2_2 I J g = Yca4_5_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_5_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xa4_5_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_4_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xca4_5_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ya4_5_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yca4_5_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_2_2 TL4_5_2 YLa4_5_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (2 : ZMod 8)).1 (realSize (5 : ZMod 8) (2 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_2_3 : ∀ I J g, Xa4_5_2_3 I J g = Xca4_5_2_3 I J g := by
  decide +kernel

theorem hYtaba4_5_2_3 : ∀ I J g, Ya4_5_2_3 I J g = Yca4_5_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_5_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xa4_5_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_4_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xca4_5_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ya4_5_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yca4_5_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_2_3 TL4_5_2 YLa4_5_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_0 : ∀ I J g, Xb4_5_2_0 I J g = Xcb4_5_2_0 I J g := by
  decide +kernel

theorem hYtabb4_5_2_0 : ∀ I J g, Yb4_5_2_0 I J g = Ycb4_5_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_5_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_0 TL4_5_2 YLb4_5_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_1 : ∀ I J g, Xb4_5_2_1 I J g = Xcb4_5_2_1 I J g := by
  decide +kernel

theorem hYtabb4_5_2_1 : ∀ I J g, Yb4_5_2_1 I J g = Ycb4_5_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb4_5_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_1 TL4_5_2 YLb4_5_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_2 : ∀ I J g, Xb4_5_2_2 I J g = Xcb4_5_2_2 I J g := by
  decide +kernel

theorem hYtabb4_5_2_2 : ∀ I J g, Yb4_5_2_2 I J g = Ycb4_5_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb4_5_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_2 TL4_5_2 YLb4_5_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_3 : ∀ I J g, Xb4_5_2_3 I J g = Xcb4_5_2_3 I J g := by
  decide +kernel

theorem hYtabb4_5_2_3 : ∀ I J g, Yb4_5_2_3 I J g = Ycb4_5_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_5_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_3 TL4_5_2 YLb4_5_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_5_2_4 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_5_2_4 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_5_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_5_2_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_4 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_4 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_4 : ∀ I J g, Xb4_5_2_4 I J g = Xcb4_5_2_4 I J g := by
  decide +kernel

theorem hYtabb4_5_2_4 : ∀ I J g, Yb4_5_2_4 I J g = Ycb4_5_2_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb4_5_2_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_4 TL4_5_2 YLb4_5_2_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_5_2_5 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_5_2_5 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_5_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_5_2_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_5 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_5 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_5 : ∀ I J g, Xb4_5_2_5 I J g = Xcb4_5_2_5 I J g := by
  decide +kernel

theorem hYtabb4_5_2_5 : ∀ I J g, Yb4_5_2_5 I J g = Ycb4_5_2_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_5_2_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_5 TL4_5_2 YLb4_5_2_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_5_2_6 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_5_2_6 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_5_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_5_2_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_6 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_6 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_6 : ∀ I J g, Xb4_5_2_6 I J g = Xcb4_5_2_6 I J g := by
  decide +kernel

theorem hYtabb4_5_2_6 : ∀ I J g, Yb4_5_2_6 I J g = Ycb4_5_2_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_5_2_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_6 TL4_5_2 YLb4_5_2_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_5_2_7 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_5_2_7 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_5_2_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_5_2_7 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_2_7 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_2_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_2_7 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_2_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_2_7 : ∀ I J g, Xb4_5_2_7 I J g = Xcb4_5_2_7 I J g := by
  decide +kernel

theorem hYtabb4_5_2_7 : ∀ I J g, Yb4_5_2_7 I J g = Ycb4_5_2_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb4_5_2_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xb4_5_2_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcb4_5_2_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_2_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yb4_5_2_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_4_5 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycb4_5_2_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_2_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_2_7 TL4_5_2 YLb4_5_2_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_5_2_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_2_0 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_2_0 : ∀ I J g, Xc4_5_2_0 I J g = Xcc4_5_2_0 I J g := by
  decide +kernel

theorem hYtabc4_5_2_0 : ∀ I J g, Yc4_5_2_0 I J g = Ycc4_5_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_5_2_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xc4_5_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcc4_5_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yc4_5_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycc4_5_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_2_0 TL4_5_2 YLc4_5_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_5_2_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

noncomputable def Xcc4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_2_1 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_2_1 : ∀ I J g, Xc4_5_2_1 I J g = Xcc4_5_2_1 I J g := by
  decide +kernel

theorem hYtabc4_5_2_1 : ∀ I J g, Yc4_5_2_1 I J g = Ycc4_5_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc4_5_2_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xc4_5_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcc4_5_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yc4_5_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycc4_5_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_2_1 TL4_5_2 YLc4_5_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc4_5_2_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

noncomputable def Xcc4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_2_2 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_2_2 : ∀ I J g, Xc4_5_2_2 I J g = Xcc4_5_2_2 I J g := by
  decide +kernel

theorem hYtabc4_5_2_2 : ∀ I J g, Yc4_5_2_2 I J g = Ycc4_5_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc4_5_2_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xc4_5_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcc4_5_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yc4_5_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycc4_5_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_2_2 TL4_5_2 YLc4_5_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_2 (fuseRow (5 : ZMod 8) (2 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ro (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) ee) (fuseCol (5 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 2) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 I) (ri (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow ((4 : ZMod 8) + 5) (2 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc4_5_2_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_2_3 : (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_2_3 : ∀ I J g, Xc4_5_2_3 I J g = Xcc4_5_2_3 I J g := by
  decide +kernel

theorem hYtabc4_5_2_3 : ∀ I J g, Yc4_5_2_3 I J g = Ycc4_5_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc4_5_2_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T4_5_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xc4_5_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hfuseZ_5_2 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Xcc4_5_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Yc4_5_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 2)) Ycc4_5_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 2).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 2).2)) (realRepBasis ((4 : ZMod 8) + 5 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 2) (realGauge.gaugeSizeL 4 5 2).1 (realGauge.gaugeSizeL 4 5 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_2_3 TL4_5_2 YLc4_5_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_5_2 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_5_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_5_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_5_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_5_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_5_2_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_5_2 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T4_5_2
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_5_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_5_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_5_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_5_2_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_5_2_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_5_2_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_5_2_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_5_2_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_5_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T4_5_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_2 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_5_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_5_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc4_5_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc4_5_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_5_2_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 T4_5_2 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 hT4_5_2 hAint4_5_2 hBint4_5_2 hCint4_5_2

theorem gtOfT4_5_2_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 T4_5_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) hsz4_5_2 T4_5_2_ne_zero

theorem gInterSpace4_5_2_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_5_2_mem_gInterSpace, gtOfT4_5_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_5_2 : gParity ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (2 : ZMod 8) gInterSpace4_5_2_ne_bot).symm

end Triple_4_5_2

/-! ### The triple `(4,5,4)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_5 = 8`, certgen parity `0`; the transported connector literal. -/
section Triple_4_5_4
open Module
theorem hsz4_5_4 : realGauge.gaugeSizeR 4 5 4 = realGauge.gaugeSizeL 4 5 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL4_5_4 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc4_5_4 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet TL4_5_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T4_5_4 : ((realGauge.D ((4 : ZMod 8) + 5 + 4)).matrixSuper
    (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Tc4_5_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_5_4 : T4_5_4 ∈ ((realGauge.D ((4 : ZMod 8) + 5 + 4)).matrixSuper
    (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 5 + 4) Tc4_5_4 0 (by decide)

theorem T4_5_4_ne_zero : T4_5_4 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 5 + 4) Tc4_5_4 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_4_0 : ∀ I J g, Xa4_5_4_0 I J g = Xca4_5_4_0 I J g := by
  decide +kernel

theorem hYtaba4_5_4_0 : ∀ I J g, Ya4_5_4_0 I J g = Yca4_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_5_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xa4_5_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xca4_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ya4_5_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yca4_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_4_0 TL4_5_4 YLa4_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_4_1 : ∀ I J g, Xa4_5_4_1 I J g = Xca4_5_4_1 I J g := by
  decide +kernel

theorem hYtaba4_5_4_1 : ∀ I J g, Ya4_5_4_1 I J g = Yca4_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_5_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xa4_5_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_4_1 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xca4_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ya4_5_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yca4_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_4_1 TL4_5_4 YLa4_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_4_2 : ∀ I J g, Xa4_5_4_2 I J g = Xca4_5_4_2 I J g := by
  decide +kernel

theorem hYtaba4_5_4_2 : ∀ I J g, Ya4_5_4_2 I J g = Yca4_5_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_5_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xa4_5_4_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_4_1 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xca4_5_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ya4_5_4_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yca4_5_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_4_2 TL4_5_4 YLa4_5_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (4 : ZMod 8)).1 (realSize (5 : ZMod 8) (4 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_4_3 : ∀ I J g, Xa4_5_4_3 I J g = Xca4_5_4_3 I J g := by
  decide +kernel

theorem hYtaba4_5_4_3 : ∀ I J g, Ya4_5_4_3 I J g = Yca4_5_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_5_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xa4_5_4_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_4_1 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xca4_5_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ya4_5_4_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yca4_5_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_4_3 TL4_5_4 YLa4_5_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_0 : ∀ I J g, Xb4_5_4_0 I J g = Xcb4_5_4_0 I J g := by
  decide +kernel

theorem hYtabb4_5_4_0 : ∀ I J g, Yb4_5_4_0 I J g = Ycb4_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_5_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_0 TL4_5_4 YLb4_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_1 : ∀ I J g, Xb4_5_4_1 I J g = Xcb4_5_4_1 I J g := by
  decide +kernel

theorem hYtabb4_5_4_1 : ∀ I J g, Yb4_5_4_1 I J g = Ycb4_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb4_5_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_1 TL4_5_4 YLb4_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_2 : ∀ I J g, Xb4_5_4_2 I J g = Xcb4_5_4_2 I J g := by
  decide +kernel

theorem hYtabb4_5_4_2 : ∀ I J g, Yb4_5_4_2 I J g = Ycb4_5_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb4_5_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_2 TL4_5_4 YLb4_5_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_3 : ∀ I J g, Xb4_5_4_3 I J g = Xcb4_5_4_3 I J g := by
  decide +kernel

theorem hYtabb4_5_4_3 : ∀ I J g, Yb4_5_4_3 I J g = Ycb4_5_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_5_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_3 TL4_5_4 YLb4_5_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_5_4_4 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_5_4_4 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_5_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_5_4_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_4 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_4 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_4 : ∀ I J g, Xb4_5_4_4 I J g = Xcb4_5_4_4 I J g := by
  decide +kernel

theorem hYtabb4_5_4_4 : ∀ I J g, Yb4_5_4_4 I J g = Ycb4_5_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb4_5_4_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_4 TL4_5_4 YLb4_5_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_5_4_5 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_5_4_5 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_5_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_5_4_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_5 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_5 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_5 : ∀ I J g, Xb4_5_4_5 I J g = Xcb4_5_4_5 I J g := by
  decide +kernel

theorem hYtabb4_5_4_5 : ∀ I J g, Yb4_5_4_5 I J g = Ycb4_5_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_5_4_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_5 TL4_5_4 YLb4_5_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_5_4_6 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_5_4_6 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_5_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_5_4_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb4_5_4_6 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_6 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_6 : ∀ I J g, Xb4_5_4_6 I J g = Xcb4_5_4_6 I J g := by
  decide +kernel

theorem hYtabb4_5_4_6 : ∀ I J g, Yb4_5_4_6 I J g = Ycb4_5_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_5_4_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_6 TL4_5_4 YLb4_5_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_5_4_7 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_5_4_7 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_5_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_5_4_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]]]

noncomputable def Xcb4_5_4_7 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_4_7 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_4_7 : ∀ I J g, Xb4_5_4_7 I J g = Xcb4_5_4_7 I J g := by
  decide +kernel

theorem hYtabb4_5_4_7 : ∀ I J g, Yb4_5_4_7 I J g = Ycb4_5_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb4_5_4_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xb4_5_4_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcb4_5_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yb4_5_4_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_4_5 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycb4_5_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_4_7 TL4_5_4 YLb4_5_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_5_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_4_0 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_4_0 : ∀ I J g, Xc4_5_4_0 I J g = Xcc4_5_4_0 I J g := by
  decide +kernel

theorem hYtabc4_5_4_0 : ∀ I J g, Yc4_5_4_0 I J g = Ycc4_5_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_5_4_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xc4_5_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcc4_5_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yc4_5_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycc4_5_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_4_0 TL4_5_4 YLc4_5_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1]],
   [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_5_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcc4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_4_1 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_4_1 : ∀ I J g, Xc4_5_4_1 I J g = Xcc4_5_4_1 I J g := by
  decide +kernel

theorem hYtabc4_5_4_1 : ∀ I J g, Yc4_5_4_1 I J g = Ycc4_5_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc4_5_4_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xc4_5_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcc4_5_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yc4_5_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycc4_5_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_4_1 TL4_5_4 YLc4_5_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc4_5_4_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcc4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_4_2 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_4_2 : ∀ I J g, Xc4_5_4_2 I J g = Xcc4_5_4_2 I J g := by
  decide +kernel

theorem hYtabc4_5_4_2 : ∀ I J g, Yc4_5_4_2 I J g = Ycc4_5_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc4_5_4_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xc4_5_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcc4_5_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yc4_5_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycc4_5_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_4_2 TL4_5_4 YLc4_5_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_4 (fuseRow (5 : ZMod 8) (4 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ro (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) ee) (fuseCol (5 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_4_1 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 4) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 I) (ri (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow ((4 : ZMod 8) + 5) (4 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc4_5_4_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcc4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_4_3 : (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_4_3 : ∀ I J g, Xc4_5_4_3 I J g = Xcc4_5_4_3 I J g := by
  decide +kernel

theorem hYtabc4_5_4_3 : ∀ I J g, Yc4_5_4_3 I J g = Ycc4_5_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc4_5_4_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xc4_5_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hfuseZ_5_4 hfuseZ_4_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Xcc4_5_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Yc4_5_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 4)) Ycc4_5_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 4).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 4).2)) (realRepBasis ((4 : ZMod 8) + 5 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 4) (realGauge.gaugeSizeL 4 5 4).1 (realGauge.gaugeSizeL 4 5 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_4_3 TL4_5_4 YLc4_5_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_5_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_5_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_5_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_5_4_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_5_4 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T4_5_4
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_5_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_5_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_5_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_5_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_5_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_5_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_5_4_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_5_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_5_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_4 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_5_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_5_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc4_5_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc4_5_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_5_4_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 T4_5_4 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 hT4_5_4 hAint4_5_4 hBint4_5_4 hCint4_5_4

theorem gtOfT4_5_4_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 T4_5_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) hsz4_5_4 T4_5_4_ne_zero

theorem gInterSpace4_5_4_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_5_4_mem_gInterSpace, gtOfT4_5_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_5_4 : gParity ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (4 : ZMod 8) gInterSpace4_5_4_ne_bot).symm

end Triple_4_5_4

/-! ### The triple `(4,5,6)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_4_5_6
open Module
theorem hsz4_5_6 : realGauge.gaugeSizeR 4 5 6 = realGauge.gaugeSizeL 4 5 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL4_5_6 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [1, 0], [0, 0], [0, 1], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [-1, 0], [0, 0], [0, 1], [0, 0], [0, 1]],
   [[0, 0], [1, 0], [0, 0], [-1, 0], [0, 0], [0, -1], [0, 0], [0, -1]],
   [[-1, 0], [0, 0], [-1, 0], [0, 0], [0, 1], [0, 0], [0, -1], [0, 0]],
   [[0, -1], [0, 0], [0, 1], [0, 0], [-1, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, -1], [0, 0], [-1, 0], [0, 0], [1, 0]],
   [[0, 0], [0, -1], [0, 0], [0, -1], [0, 0], [1, 0], [0, 0], [-1, 0]],
   [[0, 1], [0, 0], [0, -1], [0, 0], [-1, 0], [0, 0], [-1, 0], [0, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc4_5_6 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet TL4_5_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T4_5_6 : ((realGauge.D ((4 : ZMod 8) + 5 + 6)).matrixSuper
    (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Tc4_5_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_5_6 : T4_5_6 ∈ ((realGauge.D ((4 : ZMod 8) + 5 + 6)).matrixSuper
    (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 5 + 6) Tc4_5_6 0 (by decide)

theorem T4_5_6_ne_zero : T4_5_6 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 5 + 6) Tc4_5_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_6_0 : ∀ I J g, Xa4_5_6_0 I J g = Xca4_5_6_0 I J g := by
  decide +kernel

theorem hYtaba4_5_6_0 : ∀ I J g, Ya4_5_6_0 I J g = Yca4_5_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_5_6_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xa4_5_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xca4_5_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ya4_5_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yca4_5_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_6_0 TL4_5_6 YLa4_5_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xca4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_6_1 : ∀ I J g, Xa4_5_6_1 I J g = Xca4_5_6_1 I J g := by
  decide +kernel

theorem hYtaba4_5_6_1 : ∀ I J g, Ya4_5_6_1 I J g = Yca4_5_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_5_6_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xa4_5_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xca4_5_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ya4_5_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yca4_5_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_6_1 TL4_5_6 YLa4_5_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xca4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_6_2 : ∀ I J g, Xa4_5_6_2 I J g = Xca4_5_6_2 I J g := by
  decide +kernel

theorem hYtaba4_5_6_2 : ∀ I J g, Ya4_5_6_2 I J g = Yca4_5_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_5_6_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xa4_5_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xca4_5_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ya4_5_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yca4_5_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_6_2 TL4_5_6 YLa4_5_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (6 : ZMod 8)).1 (realSize (5 : ZMod 8) (6 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_6_3 : ∀ I J g, Xa4_5_6_3 I J g = Xca4_5_6_3 I J g := by
  decide +kernel

theorem hYtaba4_5_6_3 : ∀ I J g, Ya4_5_6_3 I J g = Yca4_5_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_5_6_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xa4_5_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xca4_5_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ya4_5_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yca4_5_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa4_5_6_3 TL4_5_6 YLa4_5_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_0 : ∀ I J g, Xb4_5_6_0 I J g = Xcb4_5_6_0 I J g := by
  decide +kernel

theorem hYtabb4_5_6_0 : ∀ I J g, Yb4_5_6_0 I J g = Ycb4_5_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_5_6_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_0 TL4_5_6 YLb4_5_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_1 : ∀ I J g, Xb4_5_6_1 I J g = Xcb4_5_6_1 I J g := by
  decide +kernel

theorem hYtabb4_5_6_1 : ∀ I J g, Yb4_5_6_1 I J g = Ycb4_5_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb4_5_6_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_1 TL4_5_6 YLb4_5_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_2 : ∀ I J g, Xb4_5_6_2 I J g = Xcb4_5_6_2 I J g := by
  decide +kernel

theorem hYtabb4_5_6_2 : ∀ I J g, Yb4_5_6_2 I J g = Ycb4_5_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb4_5_6_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_2 TL4_5_6 YLb4_5_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_3 : ∀ I J g, Xb4_5_6_3 I J g = Xcb4_5_6_3 I J g := by
  decide +kernel

theorem hYtabb4_5_6_3 : ∀ I J g, Yb4_5_6_3 I J g = Ycb4_5_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_5_6_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_3 TL4_5_6 YLb4_5_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_5_6_4 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_5_6_4 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_5_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_5_6_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_4 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_4 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_4 : ∀ I J g, Xb4_5_6_4 I J g = Xcb4_5_6_4 I J g := by
  decide +kernel

theorem hYtabb4_5_6_4 : ∀ I J g, Yb4_5_6_4 I J g = Ycb4_5_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb4_5_6_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_4 TL4_5_6 YLb4_5_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_5_6_5 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_5_6_5 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_5_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_5_6_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_5 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_5 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_5 : ∀ I J g, Xb4_5_6_5 I J g = Xcb4_5_6_5 I J g := by
  decide +kernel

theorem hYtabb4_5_6_5 : ∀ I J g, Yb4_5_6_5 I J g = Ycb4_5_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_5_6_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_5 TL4_5_6 YLb4_5_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_5_6_6 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_5_6_6 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_5_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_5_6_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcb4_5_6_6 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_6 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_6 : ∀ I J g, Xb4_5_6_6 I J g = Xcb4_5_6_6 I J g := by
  decide +kernel

theorem hYtabb4_5_6_6 : ∀ I J g, Yb4_5_6_6 I J g = Ycb4_5_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_5_6_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_6 TL4_5_6 YLb4_5_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_5_6_7 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_5_6_7 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_5_6_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_5_6_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb4_5_6_7 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_6_7 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_6_7 : ∀ I J g, Xb4_5_6_7 I J g = Xcb4_5_6_7 I J g := by
  decide +kernel

theorem hYtabb4_5_6_7 : ∀ I J g, Yb4_5_6_7 I J g = Ycb4_5_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb4_5_6_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xb4_5_6_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcb4_5_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yb4_5_6_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_4_5 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycb4_5_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb4_5_6_7 TL4_5_6 YLb4_5_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_5_6_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_6_0 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_6_0 : ∀ I J g, Xc4_5_6_0 I J g = Xcc4_5_6_0 I J g := by
  decide +kernel

theorem hYtabc4_5_6_0 : ∀ I J g, Yc4_5_6_0 I J g = Ycc4_5_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_5_6_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xc4_5_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcc4_5_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yc4_5_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycc4_5_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_6_0 TL4_5_6 YLc4_5_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_5_6_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_6_1 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_6_1 : ∀ I J g, Xc4_5_6_1 I J g = Xcc4_5_6_1 I J g := by
  decide +kernel

theorem hYtabc4_5_6_1 : ∀ I J g, Yc4_5_6_1 I J g = Ycc4_5_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc4_5_6_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xc4_5_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcc4_5_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yc4_5_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycc4_5_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_6_1 TL4_5_6 YLc4_5_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc4_5_6_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_6_2 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_6_2 : ∀ I J g, Xc4_5_6_2 I J g = Xcc4_5_6_2 I J g := by
  decide +kernel

theorem hYtabc4_5_6_2 : ∀ I J g, Yc4_5_6_2 I J g = Ycc4_5_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc4_5_6_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xc4_5_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcc4_5_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yc4_5_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycc4_5_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_6_2 TL4_5_6 YLc4_5_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_6 (fuseRow (5 : ZMod 8) (6 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ro (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) ee) (fuseCol (5 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 6) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 I) (ri (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow ((4 : ZMod 8) + 5) (6 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc4_5_6_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_6_3 : (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_6_3 : ∀ I J g, Xc4_5_6_3 I J g = Xcc4_5_6_3 I J g := by
  decide +kernel

theorem hYtabc4_5_6_3 : ∀ I J g, Yc4_5_6_3 I J g = Ycc4_5_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc4_5_6_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T4_5_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xc4_5_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hfuseZ_5_6 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Xcc4_5_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Yc4_5_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 6)) Ycc4_5_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 6).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 6).2)) (realRepBasis ((4 : ZMod 8) + 5 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 6) (realGauge.gaugeSizeL 4 5 6).1 (realGauge.gaugeSizeL 4 5 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc4_5_6_3 TL4_5_6 YLc4_5_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_5_6 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_5_6
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_5_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_5_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_5_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_5_6_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_5_6 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T4_5_6
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_5_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_5_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_5_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_5_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_5_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_5_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_5_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_5_6_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_5_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T4_5_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T4_5_6 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_5_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_5_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc4_5_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc4_5_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_5_6_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 T4_5_6 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 hT4_5_6 hAint4_5_6 hBint4_5_6 hCint4_5_6

theorem gtOfT4_5_6_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 T4_5_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) hsz4_5_6 T4_5_6_ne_zero

theorem gInterSpace4_5_6_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_5_6_mem_gInterSpace, gtOfT4_5_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_5_6 : gParity ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (6 : ZMod 8) gInterSpace4_5_6_ne_bot).symm

end Triple_4_5_6

/-! ### The triple `(4,5,7)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_4_5_7
open Module
theorem hsz4_5_7 : realGauge.gaugeSizeR 4 5 7 = realGauge.gaugeSizeL 4 5 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL4_5_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [-1], [0]],
   [[0], [0], [0], [0], [1], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [-1]],
   [[0], [0], [0], [0], [0], [1], [0], [-1]],
   [[0], [1], [0], [1], [0], [0], [0], [0]],
   [[0], [1], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [-1], [0], [0], [0], [0], [0]],
   [[-1], [0], [-1], [0], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc4_5_7 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet TL4_5_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T4_5_7 : ((realGauge.D ((4 : ZMod 8) + 5 + 7)).matrixSuper
    (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2).carrier :=
  matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Tc4_5_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT4_5_7 : T4_5_7 ∈ ((realGauge.D ((4 : ZMod 8) + 5 + 7)).matrixSuper
    (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((4 : ZMod 8) + 5 + 7) Tc4_5_7 1 (by decide)

theorem T4_5_7_ne_zero : T4_5_7 ≠ 0 :=
  matOfCoeff_ne_zero ((4 : ZMod 8) + 5 + 7) Tc4_5_7 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_7_0 : ∀ I J g, Xa4_5_7_0 I J g = Xca4_5_7_0 I J g := by
  decide +kernel

theorem hYtaba4_5_7_0 : ∀ I J g, Ya4_5_7_0 I J g = Yca4_5_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta4_5_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xa4_5_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xca4_5_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ya4_5_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yca4_5_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_7_0 TL4_5_7 YLa4_5_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xca4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_7_1 : ∀ I J g, Xa4_5_7_1 I J g = Xca4_5_7_1 I J g := by
  decide +kernel

theorem hYtaba4_5_7_1 : ∀ I J g, Ya4_5_7_1 I J g = Yca4_5_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta4_5_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xa4_5_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xca4_5_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ya4_5_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yca4_5_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_7_1 TL4_5_7 YLa4_5_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa4_5_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa4_5_7_2 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xca4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_7_2 : ∀ I J g, Xa4_5_7_2 I J g = Xca4_5_7_2 I J g := by
  decide +kernel

theorem hYtaba4_5_7_2 : ∀ I J g, Ya4_5_7_2 I J g = Yca4_5_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta4_5_7_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xa4_5_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xca4_5_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ya4_5_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yca4_5_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_7_2 TL4_5_7 YLa4_5_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) = (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) then
      ((sgn (sumParity (realSize (5 : ZMod 8) (7 : ZMod 8)).1 (realSize (5 : ZMod 8) (7 : ZMod 8)).2 (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa4_5_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa4_5_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xca4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa4_5_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa4_5_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba4_5_7_3 : ∀ I J g, Xa4_5_7_3 I J g = Xca4_5_7_3 I J g := by
  decide +kernel

theorem hYtaba4_5_7_3 : ∀ I J g, Ya4_5_7_3 I J g = Yca4_5_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta4_5_7_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xa4_5_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xca4_5_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba4_5_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ya4_5_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yca4_5_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba4_5_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa4_5_7_3 TL4_5_7 YLa4_5_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_0 : ∀ I J g, Xb4_5_7_0 I J g = Xcb4_5_7_0 I J g := by
  decide +kernel

theorem hYtabb4_5_7_0 : ∀ I J g, Yb4_5_7_0 I J g = Ycb4_5_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb4_5_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_0 TL4_5_7 YLb4_5_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_1 : ∀ I J g, Xb4_5_7_1 I J g = Xcb4_5_7_1 I J g := by
  decide +kernel

theorem hYtabb4_5_7_1 : ∀ I J g, Yb4_5_7_1 I J g = Ycb4_5_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb4_5_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_1 TL4_5_7 YLb4_5_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb4_5_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb4_5_7_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_2 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_2 : ∀ I J g, Xb4_5_7_2 I J g = Xcb4_5_7_2 I J g := by
  decide +kernel

theorem hYtabb4_5_7_2 : ∀ I J g, Yb4_5_7_2 I J g = Ycb4_5_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb4_5_7_2 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_2 TL4_5_7 YLb4_5_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb4_5_7_3 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb4_5_7_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcb4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_3 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_3 : ∀ I J g, Xb4_5_7_3 I J g = Xcb4_5_7_3 I J g := by
  decide +kernel

theorem hYtabb4_5_7_3 : ∀ I J g, Yb4_5_7_3 I J g = Ycb4_5_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb4_5_7_3 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_3 TL4_5_7 YLb4_5_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb4_5_7_4 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb4_5_7_4 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb4_5_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb4_5_7_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb4_5_7_4 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_4 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_4 : ∀ I J g, Xb4_5_7_4 I J g = Xcb4_5_7_4 I J g := by
  decide +kernel

theorem hYtabb4_5_7_4 : ∀ I J g, Yb4_5_7_4 I J g = Ycb4_5_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb4_5_7_4 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_4 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_4 TL4_5_7 YLb4_5_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb4_5_7_5 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb4_5_7_5 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb4_5_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb4_5_7_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb4_5_7_5 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_5 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_5 : ∀ I J g, Xb4_5_7_5 I J g = Xcb4_5_7_5 I J g := by
  decide +kernel

theorem hYtabb4_5_7_5 : ∀ I J g, Yb4_5_7_5 I J g = Ycb4_5_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb4_5_7_5 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_5 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_5 TL4_5_7 YLb4_5_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb4_5_7_6 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb4_5_7_6 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb4_5_7_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb4_5_7_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcb4_5_7_6 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_6 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_6 : ∀ I J g, Xb4_5_7_6 I J g = Xcb4_5_7_6 I J g := by
  decide +kernel

theorem hYtabb4_5_7_6 : ∀ I J g, Yb4_5_7_6 I J g = Ycb4_5_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb4_5_7_6 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_6 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_6 TL4_5_7 YLb4_5_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb4_5_7_7 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb4_5_7_7 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_5 (fuseRow (4 : ZMod 8) (5 : ZMod 8) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (4 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb4_5_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb4_5_7_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

noncomputable def Xcb4_5_7_7 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb4_5_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb4_5_7_7 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb4_5_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb4_5_7_7 : ∀ I J g, Xb4_5_7_7 I J g = Xcb4_5_7_7 I J g := by
  decide +kernel

theorem hYtabb4_5_7_7 : ∀ I J g, Yb4_5_7_7 I J g = Ycb4_5_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb4_5_7_7 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xb4_5_7_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcb4_5_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb4_5_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yb4_5_7_7 := Matrix.ext fun I J => routeL_bSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_4_5 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycb4_5_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb4_5_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb4_5_7_7 TL4_5_7 YLb4_5_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc4_5_7_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_7_0 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_7_0 : ∀ I J g, Xc4_5_7_0 I J g = Xcc4_5_7_0 I J g := by
  decide +kernel

theorem hYtabc4_5_7_0 : ∀ I J g, Yc4_5_7_0 I J g = Ycc4_5_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc4_5_7_0 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xc4_5_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcc4_5_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yc4_5_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycc4_5_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_7_0 TL4_5_7 YLc4_5_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_5_7 (fuseRow (5 : ZMod 8) (7 : ZMod 8) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ro (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) ee) (fuseCol (5 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow (4 : ZMod 8) ((5 : ZMod 8) + 7) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 I) (ri (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 J) g) (fuseCol (4 : ZMod 8) ((5 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun I J g => if (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) = (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (5 : ZMod 8)).1 (realSize (4 : ZMod 8) (5 : ZMod 8)).2 (lo (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow ((4 : ZMod 8) + 5) (7 : ZMod 8) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) I) (li (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((4 : ZMod 8) + 5) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc4_5_7_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc4_5_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc4_5_7_1 : (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2) → Fin (realRepDim ((4 : ZMod 8) + 5 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc4_5_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc4_5_7_1 : ∀ I J g, Xc4_5_7_1 I J g = Xcc4_5_7_1 I J g := by
  decide +kernel

theorem hYtabc4_5_7_1 : ∀ I J g, Yc4_5_7_1 I J g = Ycc4_5_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc4_5_7_1 :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T4_5_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xc4_5_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hfuseZ_5_7 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Xcc4_5_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc4_5_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Yc4_5_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((4 : ZMod 8) + 5 + 7)) Ycc4_5_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 4 5 7).1 ⊕ Fin (realGauge.gaugeSizeL 4 5 7).2)) (realRepBasis ((4 : ZMod 8) + 5 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc4_5_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((4 : ZMod 8) + 5 + 7) (realGauge.gaugeSizeL 4 5 7).1 (realGauge.gaugeSizeL 4 5 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc4_5_7_1 TL4_5_7 YLc4_5_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint4_5_7 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T4_5_7
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hinta4_5_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hinta4_5_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hinta4_5_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hinta4_5_7_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint4_5_7 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T4_5_7
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintb4_5_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintb4_5_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintb4_5_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintb4_5_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintb4_5_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintb4_5_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintb4_5_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintb4_5_7_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint4_5_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T4_5_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T4_5_7 * (realGauge.gaugeRouteL (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc4_5_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc4_5_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT4_5_7_mem_gInterSpace :
    gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 T4_5_7 ∈ gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 hT4_5_7 hAint4_5_7 hBint4_5_7 hCint4_5_7

theorem gtOfT4_5_7_ne_zero : gtOfT ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 T4_5_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) hsz4_5_7 T4_5_7_ne_zero

theorem gInterSpace4_5_7_ne_bot : gInterSpace ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT4_5_7_mem_gInterSpace, gtOfT4_5_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_4_5_7 : gParity ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (4 : ZMod 8) (5 : ZMod 8) (7 : ZMod 8) gInterSpace4_5_7_ne_bot).symm

end Triple_4_5_7

end G4_9
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G4_9.gParity_4_5_2
#print axioms Superfusion.GaugeChi.TripleCerts.G4_9.gParity_4_5_4
#print axioms Superfusion.GaugeChi.TripleCerts.G4_9.gParity_4_5_6
#print axioms Superfusion.GaugeChi.TripleCerts.G4_9.gParity_4_5_7
