/-
Superfusion / GaugeChi / TripleCerts / G3_1

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 3,2,3 \
        --module G3_1 \
        --out Superfusion/GaugeChi/TripleCerts/G3_1.lean

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

Triples (1): (3,2,3).
No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteBridgeProto
import Superfusion.GaugeChi.TripleCerts.FuseShadows

namespace Superfusion
namespace GaugeChi
namespace TripleCerts
namespace G3_1

open Module

/-! ### The fusion shadows this batch uses (4 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_2_3`, `fuseZ_3_2`, `fuseZ_3_5`, `fuseZ_5_3`. -/

/-! ### The triple `(3,2,3)`

`gaugeSizeL = gaugeSizeR = (8,8)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_3_2_3
open Module
theorem hsz3_2_3 : realGauge.gaugeSizeR 3 2 3 = realGauge.gaugeSizeL 3 2 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`16 x 16 x 1`). -/
def TL3_2_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 8 ⊕ Fin 8`. -/
noncomputable def Tc3_2_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet TL3_2_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T3_2_3 : ((realGauge.D ((3 : ZMod 8) + 2 + 3)).matrixSuper
    (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2).carrier :=
  matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Tc3_2_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT3_2_3 : T3_2_3 ∈ ((realGauge.D ((3 : ZMod 8) + 2 + 3)).matrixSuper
    (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((3 : ZMod 8) + 2 + 3) Tc3_2_3 1 (by decide)

theorem T3_2_3_ne_zero : T3_2_3 ≠ 0 :=
  matOfCoeff_ne_zero ((3 : ZMod 8) + 2 + 3) Tc3_2_3 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨2, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_0 : ∀ I J g, Xa3_2_3_0 I J g = Xca3_2_3_0 I J g := by
  decide +kernel

theorem hYtaba3_2_3_0 : ∀ I J g, Ya3_2_3_0 I J g = Yca3_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta3_2_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_0 TL3_2_3 YLa3_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_1 : ∀ I J g, Xa3_2_3_1 I J g = Xca3_2_3_1 I J g := by
  decide +kernel

theorem hYtaba3_2_3_1 : ∀ I J g, Ya3_2_3_1 I J g = Yca3_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta3_2_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_1 TL3_2_3 YLa3_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_2 : ∀ I J g, Xa3_2_3_2 I J g = Xca3_2_3_2 I J g := by
  decide +kernel

theorem hYtaba3_2_3_2 : ∀ I J g, Ya3_2_3_2 I J g = Yca3_2_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta3_2_3_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_2 TL3_2_3 YLa3_2_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xca3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_3 : ∀ I J g, Xa3_2_3_3 I J g = Xca3_2_3_3 I J g := by
  decide +kernel

theorem hYtaba3_2_3_3 : ∀ I J g, Ya3_2_3_3 I J g = Yca3_2_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta3_2_3_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_3 TL3_2_3 YLa3_2_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Xa3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `4`. -/
noncomputable def Ya3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `4`, pre-tabulated. -/
def XLa3_2_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `4`, pre-tabulated. -/
def YLa3_2_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_4 : ∀ I J g, Xa3_2_3_4 I J g = Xca3_2_3_4 I J g := by
  decide +kernel

theorem hYtaba3_2_3_4 : ∀ I J g, Ya3_2_3_4 I J g = Yca3_2_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `4`** (Koszul sign `-1`). -/
theorem hinta3_2_3_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_4 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_4 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_4 TL3_2_3 YLa3_2_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Xa3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `5`. -/
noncomputable def Ya3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `5`, pre-tabulated. -/
def XLa3_2_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]]]

/-- Left route at the `a`-slot generator `5`, pre-tabulated. -/
def YLa3_2_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_5 : ∀ I J g, Xa3_2_3_5 I J g = Xca3_2_3_5 I J g := by
  decide +kernel

theorem hYtaba3_2_3_5 : ∀ I J g, Ya3_2_3_5 I J g = Yca3_2_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `5`** (Koszul sign `+1`). -/
theorem hinta3_2_3_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_5 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_5 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_5 TL3_2_3 YLa3_2_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Xa3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `6`. -/
noncomputable def Ya3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `6`, pre-tabulated. -/
def XLa3_2_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `6`, pre-tabulated. -/
def YLa3_2_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_6 : ∀ I J g, Xa3_2_3_6 I J g = Xca3_2_3_6 I J g := by
  decide +kernel

theorem hYtaba3_2_3_6 : ∀ I J g, Ya3_2_3_6 I J g = Yca3_2_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `6`** (Koszul sign `+1`). -/
theorem hinta3_2_3_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_6 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_6 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_6 TL3_2_3 YLa3_2_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Xa3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) = (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `7`. -/
noncomputable def Ya3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `7`, pre-tabulated. -/
def XLa3_2_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `7`, pre-tabulated. -/
def YLa3_2_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa3_2_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Yca3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa3_2_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba3_2_3_7 : ∀ I J g, Xa3_2_3_7 I J g = Xca3_2_3_7 I J g := by
  decide +kernel

theorem hYtaba3_2_3_7 : ∀ I J g, Ya3_2_3_7 I J g = Yca3_2_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `7`** (Koszul sign `-1`). -/
theorem hinta3_2_3_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xa3_2_3_7 := Matrix.ext fun I J => routeR'_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_3_5 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xca3_2_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba3_2_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ya3_2_3_7 := Matrix.ext fun I J => routeL_aSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yca3_2_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba3_2_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa3_2_3_7 TL3_2_3 YLa3_2_3_7 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_3_0 : ∀ I J g, Xb3_2_3_0 I J g = Xcb3_2_3_0 I J g := by
  decide +kernel

theorem hYtabb3_2_3_0 : ∀ I J g, Yb3_2_3_0 I J g = Ycb3_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb3_2_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xb3_2_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcb3_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yb3_2_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycb3_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_2_3_0 TL3_2_3 YLb3_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_3_1 : ∀ I J g, Xb3_2_3_1 I J g = Xcb3_2_3_1 I J g := by
  decide +kernel

theorem hYtabb3_2_3_1 : ∀ I J g, Yb3_2_3_1 I J g = Ycb3_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb3_2_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xb3_2_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcb3_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yb3_2_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycb3_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_2_3_1 TL3_2_3 YLb3_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_3_2 : ∀ I J g, Xb3_2_3_2 I J g = Xcb3_2_3_2 I J g := by
  decide +kernel

theorem hYtabb3_2_3_2 : ∀ I J g, Yb3_2_3_2 I J g = Ycb3_2_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb3_2_3_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xb3_2_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcb3_2_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yb3_2_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycb3_2_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_2_3_2 TL3_2_3 YLb3_2_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_2 (fuseRow (3 : ZMod 8) (2 : ZMod 8) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (3 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb3_2_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb3_2_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb3_2_3_3 : ∀ I J g, Xb3_2_3_3 I J g = Xcb3_2_3_3 I J g := by
  decide +kernel

theorem hYtabb3_2_3_3 : ∀ I J g, Yb3_2_3_3 I J g = Ycb3_2_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb3_2_3_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xb3_2_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcb3_2_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb3_2_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yb3_2_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_3_2 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycb3_2_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb3_2_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb3_2_3_3 TL3_2_3 YLb3_2_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc3_2_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_0 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_0 : ∀ I J g, Xc3_2_3_0 I J g = Xcc3_2_3_0 I J g := by
  decide +kernel

theorem hYtabc3_2_3_0 : ∀ I J g, Yc3_2_3_0 I J g = Ycc3_2_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc3_2_3_0 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_0 TL3_2_3 YLc3_2_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc3_2_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_1 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_1 : ∀ I J g, Xc3_2_3_1 I J g = Xcc3_2_3_1 I J g := by
  decide +kernel

theorem hYtabc3_2_3_1 : ∀ I J g, Yc3_2_3_1 I J g = Ycc3_2_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc3_2_3_1 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_1 TL3_2_3 YLc3_2_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc3_2_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_2 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_2 : ∀ I J g, Xc3_2_3_2 I J g = Xcc3_2_3_2 I J g := by
  decide +kernel

theorem hYtabc3_2_3_2 : ∀ I J g, Yc3_2_3_2 I J g = Ycc3_2_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc3_2_3_2 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_2 TL3_2_3 YLc3_2_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc3_2_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcc3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_3 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_3 : ∀ I J g, Xc3_2_3_3 I J g = Xcc3_2_3_3 I J g := by
  decide +kernel

theorem hYtabc3_2_3_3 : ∀ I J g, Yc3_2_3_3 I J g = Ycc3_2_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc3_2_3_3 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_3 TL3_2_3 YLc3_2_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc3_2_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc3_2_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_4 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_4 : ∀ I J g, Xc3_2_3_4 I J g = Xcc3_2_3_4 I J g := by
  decide +kernel

theorem hYtabc3_2_3_4 : ∀ I J g, Yc3_2_3_4 I J g = Ycc3_2_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintc3_2_3_4 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_4 TL3_2_3 YLc3_2_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc3_2_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc3_2_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcc3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_5 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_5 : ∀ I J g, Xc3_2_3_5 I J g = Xcc3_2_3_5 I J g := by
  decide +kernel

theorem hYtabc3_2_3_5 : ∀ I J g, Yc3_2_3_5 I J g = Ycc3_2_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc3_2_3_5 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_5 TL3_2_3 YLc3_2_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc3_2_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc3_2_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_6 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_6 : ∀ I J g, Xc3_2_3_6 I J g = Xcc3_2_3_6 I J g := by
  decide +kernel

theorem hYtabc3_2_3_6 : ∀ I J g, Yc3_2_3_6 I J g = Ycc3_2_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc3_2_3_6 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_6 TL3_2_3 YLc3_2_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ro (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_3_5 (fuseRow (3 : ZMod 8) ((2 : ZMod 8) + 3) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 I) (ri (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 J) g) (fuseCol (3 : ZMod 8) ((2 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun I J g => if (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) = (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (2 : ZMod 8)).1 (realSize (3 : ZMod 8) (2 : ZMod 8)).2 (lo (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((3 : ZMod 8) + 2) (3 : ZMod 8) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) I) (li (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((3 : ZMod 8) + 2) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc3_2_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc3_2_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc3_2_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc3_2_3_7 : (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2) → Fin (realRepDim ((3 : ZMod 8) + 2 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc3_2_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `16² · 1 = 256` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc3_2_3_7 : ∀ I J g, Xc3_2_3_7 I J g = Xcc3_2_3_7 I J g := by
  decide +kernel

theorem hYtabc3_2_3_7 : ∀ I J g, Yc3_2_3_7 I J g = Ycc3_2_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintc3_2_3_7 :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xc3_2_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hfuseZ_2_3 hfuseZ_3_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Xcc3_2_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc3_2_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Yc3_2_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((3 : ZMod 8) + 2 + 3)) Ycc3_2_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 3 2 3).1 ⊕ Fin (realGauge.gaugeSizeL 3 2 3).2)) (realRepBasis ((3 : ZMod 8) + 2 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc3_2_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((3 : ZMod 8) + 2 + 3) (realGauge.gaugeSizeL 3 2 3).1 (realGauge.gaugeSizeL 3 2 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc3_2_3_7 TL3_2_3 YLc3_2_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint3_2_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hinta3_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hinta3_2_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hinta3_2_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hinta3_2_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hinta3_2_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hinta3_2_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hinta3_2_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hinta3_2_3_7

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint3_2_3 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T3_2_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintb3_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintb3_2_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintb3_2_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintb3_2_3_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint3_2_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T3_2_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T3_2_3 * (realGauge.gaugeRouteL (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc3_2_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc3_2_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc3_2_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc3_2_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc3_2_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc3_2_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc3_2_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc3_2_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT3_2_3_mem_gInterSpace :
    gtOfT ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 T3_2_3 ∈ gInterSpace ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 hT3_2_3 hAint3_2_3 hBint3_2_3 hCint3_2_3

theorem gtOfT3_2_3_ne_zero : gtOfT ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 T3_2_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) hsz3_2_3 T3_2_3_ne_zero

theorem gInterSpace3_2_3_ne_bot : gInterSpace ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT3_2_3_mem_gInterSpace, gtOfT3_2_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_3_2_3 : gParity ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (3 : ZMod 8) (2 : ZMod 8) (3 : ZMod 8) gInterSpace3_2_3_ne_bot).symm

end Triple_3_2_3

end G3_1
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G3_1.gParity_3_2_3
