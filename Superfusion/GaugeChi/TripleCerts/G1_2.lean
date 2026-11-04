/-
Superfusion / GaugeChi / TripleCerts / G1_2

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 1,3,3 1,3,4 1,3,5 1,3,7 1,4,0 1,4,1 1,4,3 \
        --module G1_2 \
        --out Superfusion/GaugeChi/TripleCerts/G1_2.lean

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

Triples (7): (1,3,3), (1,3,4), (1,3,5), (1,3,7), (1,4,0), (1,4,1), (1,4,3).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (1,4,0).
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
namespace G1_2

open Module

/-! ### The fusion shadows this batch uses (20 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_1_0`, `fuseZ_1_2`, `fuseZ_1_3`, `fuseZ_1_4`, `fuseZ_1_5`, `fuseZ_1_6`, `fuseZ_1_7`, `fuseZ_3_3`, `fuseZ_3_4`, `fuseZ_3_5`, `fuseZ_3_7`, `fuseZ_4_0`, `fuseZ_4_1`, `fuseZ_4_3`, `fuseZ_4_4`, `fuseZ_4_5`, `fuseZ_4_7`, `fuseZ_5_0`, `fuseZ_5_1`, `fuseZ_5_3`. -/

/-! ### The triple `(1,3,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_7 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_1_3_3
open Module
theorem hsz1_3_3 : realGauge.gaugeSizeR 1 3 3 = realGauge.gaugeSizeL 1 3 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL1_3_3 : List (List (List ℤ)) :=
  [[[1, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 1]],
   [[0, 0], [0, 0], [1, 0], [1, 0], [0, -1], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [1, 0], [0, 1], [0, 1], [0, 0], [0, 0]],
   [[-1, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 1]],
   [[0, 1], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 1], [1, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, -1], [1, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc1_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet TL1_3_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T1_3_3 : ((realGauge.D ((1 : ZMod 8) + 3 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Tc1_3_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_3_3 : T1_3_3 ∈ ((realGauge.D ((1 : ZMod 8) + 3 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 3 + 3) Tc1_3_3 0 (by decide)

theorem T1_3_3_ne_zero : T1_3_3 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 3 + 3) Tc1_3_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (3 : ZMod 8)).1 (realSize (3 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_3_0 : ∀ I J g, Xa1_3_3_0 I J g = Xca1_3_3_0 I J g := by
  decide +kernel

theorem hYtaba1_3_3_0 : ∀ I J g, Ya1_3_3_0 I J g = Yca1_3_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_3_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xa1_3_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xca1_3_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ya1_3_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yca1_3_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_3_0 TL1_3_3 YLa1_3_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (3 : ZMod 8)).1 (realSize (3 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_3_1 : ∀ I J g, Xa1_3_3_1 I J g = Xca1_3_3_1 I J g := by
  decide +kernel

theorem hYtaba1_3_3_1 : ∀ I J g, Ya1_3_3_1 I J g = Yca1_3_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_3_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xa1_3_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xca1_3_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ya1_3_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yca1_3_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_3_1 TL1_3_3 YLa1_3_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_0 : ∀ I J g, Xb1_3_3_0 I J g = Xcb1_3_3_0 I J g := by
  decide +kernel

theorem hYtabb1_3_3_0 : ∀ I J g, Yb1_3_3_0 I J g = Ycb1_3_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_3_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_0 TL1_3_3 YLb1_3_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_1 : ∀ I J g, Xb1_3_3_1 I J g = Xcb1_3_3_1 I J g := by
  decide +kernel

theorem hYtabb1_3_3_1 : ∀ I J g, Yb1_3_3_1 I J g = Ycb1_3_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_3_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_1 TL1_3_3 YLb1_3_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_3_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_3_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_2 : ∀ I J g, Xb1_3_3_2 I J g = Xcb1_3_3_2 I J g := by
  decide +kernel

theorem hYtabb1_3_3_2 : ∀ I J g, Yb1_3_3_2 I J g = Ycb1_3_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_3_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_2 TL1_3_3 YLb1_3_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_3_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_3_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_3 : ∀ I J g, Xb1_3_3_3 I J g = Xcb1_3_3_3 I J g := by
  decide +kernel

theorem hYtabb1_3_3_3 : ∀ I J g, Yb1_3_3_3 I J g = Ycb1_3_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_3_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_3 TL1_3_3 YLb1_3_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_3_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_3_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_4 : ∀ I J g, Xb1_3_3_4 I J g = Xcb1_3_3_4 I J g := by
  decide +kernel

theorem hYtabb1_3_3_4 : ∀ I J g, Yb1_3_3_4 I J g = Ycb1_3_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb1_3_3_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_4 TL1_3_3 YLb1_3_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_3_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_3_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_5 : ∀ I J g, Xb1_3_3_5 I J g = Xcb1_3_3_5 I J g := by
  decide +kernel

theorem hYtabb1_3_3_5 : ∀ I J g, Yb1_3_3_5 I J g = Ycb1_3_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_3_3_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_5 TL1_3_3 YLb1_3_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_3_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_3_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_6 : ∀ I J g, Xb1_3_3_6 I J g = Xcb1_3_3_6 I J g := by
  decide +kernel

theorem hYtabb1_3_3_6 : ∀ I J g, Yb1_3_3_6 I J g = Ycb1_3_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_3_3_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_6 TL1_3_3 YLb1_3_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_3_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_3_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_3_7 : ∀ I J g, Xb1_3_3_7 I J g = Xcb1_3_3_7 I J g := by
  decide +kernel

theorem hYtabb1_3_3_7 : ∀ I J g, Yb1_3_3_7 I J g = Ycb1_3_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb1_3_3_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xb1_3_3_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcb1_3_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yb1_3_3_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_1_3 hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycb1_3_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_3_7 TL1_3_3 YLb1_3_3_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_3_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_0 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_0 : ∀ I J g, Xc1_3_3_0 I J g = Xcc1_3_3_0 I J g := by
  decide +kernel

theorem hYtabc1_3_3_0 : ∀ I J g, Yc1_3_3_0 I J g = Ycc1_3_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_3_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_0 TL1_3_3 YLc1_3_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_3_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_1 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_1 : ∀ I J g, Xc1_3_3_1 I J g = Xcc1_3_3_1 I J g := by
  decide +kernel

theorem hYtabc1_3_3_1 : ∀ I J g, Yc1_3_3_1 I J g = Ycc1_3_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_3_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_1 TL1_3_3 YLc1_3_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_3_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_3_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_2 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_2 : ∀ I J g, Xc1_3_3_2 I J g = Xcc1_3_3_2 I J g := by
  decide +kernel

theorem hYtabc1_3_3_2 : ∀ I J g, Yc1_3_3_2 I J g = Ycc1_3_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_3_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_2 TL1_3_3 YLc1_3_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_3_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_3_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_3 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_3 : ∀ I J g, Xc1_3_3_3 I J g = Xcc1_3_3_3 I J g := by
  decide +kernel

theorem hYtabc1_3_3_3 : ∀ I J g, Yc1_3_3_3 I J g = Ycc1_3_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_3_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_3 TL1_3_3 YLc1_3_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_3_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_3_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_4 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_4 : ∀ I J g, Xc1_3_3_4 I J g = Xcc1_3_3_4 I J g := by
  decide +kernel

theorem hYtabc1_3_3_4 : ∀ I J g, Yc1_3_3_4 I J g = Ycc1_3_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc1_3_3_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_4 TL1_3_3 YLc1_3_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_3_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_3_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_5 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_5 : ∀ I J g, Xc1_3_3_5 I J g = Xcc1_3_3_5 I J g := by
  decide +kernel

theorem hYtabc1_3_3_5 : ∀ I J g, Yc1_3_3_5 I J g = Ycc1_3_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_3_3_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_5 TL1_3_3 YLc1_3_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_3_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_3_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_6 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_6 : ∀ I J g, Xc1_3_3_6 I J g = Xcc1_3_3_6 I J g := by
  decide +kernel

theorem hYtabc1_3_3_6 : ∀ I J g, Yc1_3_3_6 I J g = Ycc1_3_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_3_3_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_6 TL1_3_3 YLc1_3_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_3 (fuseRow (3 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ro (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) ee) (fuseCol (3 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_6 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 3) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 I) (ri (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_3 (fuseRow ((1 : ZMod 8) + 3) (3 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_3_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_3_3_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_3_7 : (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_3_7 : ∀ I J g, Xc1_3_3_7 I J g = Xcc1_3_3_7 I J g := by
  decide +kernel

theorem hYtabc1_3_3_7 : ∀ I J g, Yc1_3_3_7 I J g = Ycc1_3_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc1_3_3_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xc1_3_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hfuseZ_3_3 hfuseZ_1_6 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Xcc1_3_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Yc1_3_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hfuseZ_4_3 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 3)) Ycc1_3_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 3).2)) (realRepBasis ((1 : ZMod 8) + 3 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 3) (realGauge.gaugeSizeL 1 3 3).1 (realGauge.gaugeSizeL 1 3 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_3_7 TL1_3_3 YLc1_3_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_3_3 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_3_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_3_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_3_3_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_3_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_3_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_3_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_3_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_3_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_3_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_3_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_3_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_3_3_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_3_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_3_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_3_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_3_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_3_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_3_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_3_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_3_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_3_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_3_3_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 T1_3_3 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 hT1_3_3 hAint1_3_3 hBint1_3_3 hCint1_3_3

theorem gtOfT1_3_3_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 T1_3_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) hsz1_3_3 T1_3_3_ne_zero

theorem gInterSpace1_3_3_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_3_3_mem_gInterSpace, gtOfT1_3_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_3_3 : gParity ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (3 : ZMod 8) gInterSpace1_3_3_ne_bot).symm

end Triple_1_3_3

/-! ### The triple `(1,3,4)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `1`; the transported connector literal. -/
section Triple_1_3_4
open Module
theorem hsz1_3_4 : realGauge.gaugeSizeR 1 3 4 = realGauge.gaugeSizeL 1 3 4 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL1_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [-1], [1], [0]],
   [[0], [0], [0], [0], [0], [1], [1], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [1]],
   [[0], [-1], [-1], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [-1], [1], [0], [0], [0], [0], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc1_3_4 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet TL1_3_4 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T1_3_4 : ((realGauge.D ((1 : ZMod 8) + 3 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Tc1_3_4

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_3_4 : T1_3_4 ∈ ((realGauge.D ((1 : ZMod 8) + 3 + 4)).matrixSuper
    (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 3 + 4) Tc1_3_4 1 (by decide)

theorem T1_3_4_ne_zero : T1_3_4 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 3 + 4) Tc1_3_4 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_4_0 : ∀ I J g, Xa1_3_4_0 I J g = Xca1_3_4_0 I J g := by
  decide +kernel

theorem hYtaba1_3_4_0 : ∀ I J g, Ya1_3_4_0 I J g = Yca1_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_3_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xa1_3_4_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xca1_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ya1_3_4_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yca1_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_3_4_0 TL1_3_4 YLa1_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (4 : ZMod 8)).1 (realSize (3 : ZMod 8) (4 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_4_1 : ∀ I J g, Xa1_3_4_1 I J g = Xca1_3_4_1 I J g := by
  decide +kernel

theorem hYtaba1_3_4_1 : ∀ I J g, Ya1_3_4_1 I J g = Yca1_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta1_3_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xa1_3_4_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xca1_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ya1_3_4_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yca1_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_3_4_1 TL1_3_4 YLa1_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_0 : ∀ I J g, Xb1_3_4_0 I J g = Xcb1_3_4_0 I J g := by
  decide +kernel

theorem hYtabb1_3_4_0 : ∀ I J g, Yb1_3_4_0 I J g = Ycb1_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_3_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_0 TL1_3_4 YLb1_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_1 : ∀ I J g, Xb1_3_4_1 I J g = Xcb1_3_4_1 I J g := by
  decide +kernel

theorem hYtabb1_3_4_1 : ∀ I J g, Yb1_3_4_1 I J g = Ycb1_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb1_3_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_1 TL1_3_4 YLb1_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_3_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_3_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]]]

noncomputable def Xcb1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_2 : ∀ I J g, Xb1_3_4_2 I J g = Xcb1_3_4_2 I J g := by
  decide +kernel

theorem hYtabb1_3_4_2 : ∀ I J g, Yb1_3_4_2 I J g = Ycb1_3_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb1_3_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_2 TL1_3_4 YLb1_3_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_3_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_3_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcb1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_3 : ∀ I J g, Xb1_3_4_3 I J g = Xcb1_3_4_3 I J g := by
  decide +kernel

theorem hYtabb1_3_4_3 : ∀ I J g, Yb1_3_4_3 I J g = Ycb1_3_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_3_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_3 TL1_3_4 YLb1_3_4_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_3_4_4 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_3_4_4 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_3_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_3_4_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcb1_3_4_4 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_4 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_4 : ∀ I J g, Xb1_3_4_4 I J g = Xcb1_3_4_4 I J g := by
  decide +kernel

theorem hYtabb1_3_4_4 : ∀ I J g, Yb1_3_4_4 I J g = Ycb1_3_4_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb1_3_4_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_4 TL1_3_4 YLb1_3_4_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_3_4_5 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_3_4_5 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_3_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_3_4_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb1_3_4_5 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_5 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_5 : ∀ I J g, Xb1_3_4_5 I J g = Xcb1_3_4_5 I J g := by
  decide +kernel

theorem hYtabb1_3_4_5 : ∀ I J g, Yb1_3_4_5 I J g = Ycb1_3_4_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_3_4_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_5 TL1_3_4 YLb1_3_4_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_3_4_6 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_3_4_6 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_3_4_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_3_4_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb1_3_4_6 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_6 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_6 : ∀ I J g, Xb1_3_4_6 I J g = Xcb1_3_4_6 I J g := by
  decide +kernel

theorem hYtabb1_3_4_6 : ∀ I J g, Yb1_3_4_6 I J g = Ycb1_3_4_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_3_4_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_6 TL1_3_4 YLb1_3_4_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_3_4_7 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_3_4_7 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_3_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_3_4_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcb1_3_4_7 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_4_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_4_7 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_4_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_4_7 : ∀ I J g, Xb1_3_4_7 I J g = Xcb1_3_4_7 I J g := by
  decide +kernel

theorem hYtabb1_3_4_7 : ∀ I J g, Yb1_3_4_7 I J g = Ycb1_3_4_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb1_3_4_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xb1_3_4_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcb1_3_4_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_4_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yb1_3_4_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_1_3 hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycb1_3_4_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_4_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_4_7 TL1_3_4 YLb1_3_4_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_3_4_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_4_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_4_0 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_4_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_4_0 : ∀ I J g, Xc1_3_4_0 I J g = Xcc1_3_4_0 I J g := by
  decide +kernel

theorem hYtabc1_3_4_0 : ∀ I J g, Yc1_3_4_0 I J g = Ycc1_3_4_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_3_4_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xc1_3_4_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcc1_3_4_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_4_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yc1_3_4_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycc1_3_4_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_4_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_4_0 TL1_3_4 YLc1_3_4_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_3_4_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

noncomputable def Xcc1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_4_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_4_1 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_4_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_4_1 : ∀ I J g, Xc1_3_4_1 I J g = Xcc1_3_4_1 I J g := by
  decide +kernel

theorem hYtabc1_3_4_1 : ∀ I J g, Yc1_3_4_1 I J g = Ycc1_3_4_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_3_4_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xc1_3_4_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcc1_3_4_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_4_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yc1_3_4_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycc1_3_4_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_4_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_4_1 TL1_3_4 YLc1_3_4_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_3_4_2 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_3_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]]]

noncomputable def Xcc1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_4_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_4_2 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_4_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_4_2 : ∀ I J g, Xc1_3_4_2 I J g = Xcc1_3_4_2 I J g := by
  decide +kernel

theorem hYtabc1_3_4_2 : ∀ I J g, Yc1_3_4_2 I J g = Ycc1_3_4_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_3_4_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xc1_3_4_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcc1_3_4_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_4_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yc1_3_4_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycc1_3_4_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_4_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_4_2 TL1_3_4 YLc1_3_4_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_4 (fuseRow (3 : ZMod 8) (4 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ro (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) ee) (fuseCol (3 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 4) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 I) (ri (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 4) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I)
          * realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_4 (fuseRow ((1 : ZMod 8) + 3) (4 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_3_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_3_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_4_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_4_3 : (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 4).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_4_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_4_3 : ∀ I J g, Xc1_3_4_3 I J g = Xcc1_3_4_3 I J g := by
  decide +kernel

theorem hYtabc1_3_4_3 : ∀ I J g, Yc1_3_4_3 I J g = Ycc1_3_4_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_3_4_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xc1_3_4_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hfuseZ_3_4 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Xcc1_3_4_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_4_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Yc1_3_4_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hfuseZ_4_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 4)) Ycc1_3_4_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 4).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 4).2)) (realRepBasis ((1 : ZMod 8) + 3 + 4)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_4_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 4) (realGauge.gaugeSizeL 1 3 4).1 (realGauge.gaugeSizeL 1 3 4).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_4_3 TL1_3_4 YLc1_3_4_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_3_4 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_3_4
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_3_4_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_3_4 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_4
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_3_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_3_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_3_4_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_3_4_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_3_4_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_3_4_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_3_4_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_3_4 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_3_4
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_4 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_3_4_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_3_4_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_3_4_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_3_4_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_3_4_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 T1_3_4 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 hT1_3_4 hAint1_3_4 hBint1_3_4 hCint1_3_4

theorem gtOfT1_3_4_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 T1_3_4 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) hsz1_3_4 T1_3_4_ne_zero

theorem gInterSpace1_3_4_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_3_4_mem_gInterSpace, gtOfT1_3_4_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_3_4 : gParity ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (4 : ZMod 8) gInterSpace1_3_4_ne_bot).symm

end Triple_1_3_4

/-! ### The triple `(1,3,5)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_1 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_1_3_5
open Module
theorem hsz1_3_5 : realGauge.gaugeSizeR 1 3 5 = realGauge.gaugeSizeL 1 3 5 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL1_3_5 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 1]],
   [[0, 0], [1, 0], [0, 0], [1, 0], [0, 1], [0, 0], [0, -1], [0, 0]],
   [[1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 1]],
   [[0, 0], [-1, 0], [0, 0], [1, 0], [0, 1], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 1], [1, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 1], [0, 0], [0, -1], [0, 0], [0, 0], [1, 0], [0, 0], [1, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 1], [1, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 1], [0, 0], [0, 0], [-1, 0], [0, 0], [1, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc1_3_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet TL1_3_5 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T1_3_5 : ((realGauge.D ((1 : ZMod 8) + 3 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Tc1_3_5

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_3_5 : T1_3_5 ∈ ((realGauge.D ((1 : ZMod 8) + 3 + 5)).matrixSuper
    (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 3 + 5) Tc1_3_5 0 (by decide)

theorem T1_3_5_ne_zero : T1_3_5 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 3 + 5) Tc1_3_5 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_5_0 : ∀ I J g, Xa1_3_5_0 I J g = Xca1_3_5_0 I J g := by
  decide +kernel

theorem hYtaba1_3_5_0 : ∀ I J g, Ya1_3_5_0 I J g = Yca1_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_3_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xa1_3_5_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xca1_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ya1_3_5_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yca1_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_5_0 TL1_3_5 YLa1_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (5 : ZMod 8)).1 (realSize (3 : ZMod 8) (5 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_5_1 : ∀ I J g, Xa1_3_5_1 I J g = Xca1_3_5_1 I J g := by
  decide +kernel

theorem hYtaba1_3_5_1 : ∀ I J g, Ya1_3_5_1 I J g = Yca1_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_3_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xa1_3_5_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xca1_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ya1_3_5_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yca1_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_3_5_1 TL1_3_5 YLa1_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_0 : ∀ I J g, Xb1_3_5_0 I J g = Xcb1_3_5_0 I J g := by
  decide +kernel

theorem hYtabb1_3_5_0 : ∀ I J g, Yb1_3_5_0 I J g = Ycb1_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_3_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_0 TL1_3_5 YLb1_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_1 : ∀ I J g, Xb1_3_5_1 I J g = Xcb1_3_5_1 I J g := by
  decide +kernel

theorem hYtabb1_3_5_1 : ∀ I J g, Yb1_3_5_1 I J g = Ycb1_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_3_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_1 TL1_3_5 YLb1_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_2 : ∀ I J g, Xb1_3_5_2 I J g = Xcb1_3_5_2 I J g := by
  decide +kernel

theorem hYtabb1_3_5_2 : ∀ I J g, Yb1_3_5_2 I J g = Ycb1_3_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_3_5_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_2 TL1_3_5 YLb1_3_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_3 : ∀ I J g, Xb1_3_5_3 I J g = Xcb1_3_5_3 I J g := by
  decide +kernel

theorem hYtabb1_3_5_3 : ∀ I J g, Yb1_3_5_3 I J g = Ycb1_3_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_3_5_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_3 TL1_3_5 YLb1_3_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_4 : ∀ I J g, Xb1_3_5_4 I J g = Xcb1_3_5_4 I J g := by
  decide +kernel

theorem hYtabb1_3_5_4 : ∀ I J g, Yb1_3_5_4 I J g = Ycb1_3_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintb1_3_5_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_4 TL1_3_5 YLb1_3_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_5 : ∀ I J g, Xb1_3_5_5 I J g = Xcb1_3_5_5 I J g := by
  decide +kernel

theorem hYtabb1_3_5_5 : ∀ I J g, Yb1_3_5_5 I J g = Ycb1_3_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_3_5_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_5 TL1_3_5 YLb1_3_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_6 : ∀ I J g, Xb1_3_5_6 I J g = Xcb1_3_5_6 I J g := by
  decide +kernel

theorem hYtabb1_3_5_6 : ∀ I J g, Yb1_3_5_6 I J g = Ycb1_3_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_3_5_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_6 TL1_3_5 YLb1_3_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_5_7 : ∀ I J g, Xb1_3_5_7 I J g = Xcb1_3_5_7 I J g := by
  decide +kernel

theorem hYtabb1_3_5_7 : ∀ I J g, Yb1_3_5_7 I J g = Ycb1_3_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintb1_3_5_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xb1_3_5_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcb1_3_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yb1_3_5_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_1_3 hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycb1_3_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_3_5_7 TL1_3_5 YLb1_3_5_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_3_5_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_0 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_0 : ∀ I J g, Xc1_3_5_0 I J g = Xcc1_3_5_0 I J g := by
  decide +kernel

theorem hYtabc1_3_5_0 : ∀ I J g, Yc1_3_5_0 I J g = Ycc1_3_5_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_3_5_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_0 TL1_3_5 YLc1_3_5_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_3_5_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_1 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_1 : ∀ I J g, Xc1_3_5_1 I J g = Xcc1_3_5_1 I J g := by
  decide +kernel

theorem hYtabc1_3_5_1 : ∀ I J g, Yc1_3_5_1 I J g = Ycc1_3_5_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_3_5_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_1 TL1_3_5 YLc1_3_5_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_3_5_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_2 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_2 : ∀ I J g, Xc1_3_5_2 I J g = Xcc1_3_5_2 I J g := by
  decide +kernel

theorem hYtabc1_3_5_2 : ∀ I J g, Yc1_3_5_2 I J g = Ycc1_3_5_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_3_5_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_2 TL1_3_5 YLc1_3_5_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_3_5_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_3 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_3 : ∀ I J g, Xc1_3_5_3 I J g = Xcc1_3_5_3 I J g := by
  decide +kernel

theorem hYtabc1_3_5_3 : ∀ I J g, Yc1_3_5_3 I J g = Ycc1_3_5_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_3_5_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_3 TL1_3_5 YLc1_3_5_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_3_5_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_4 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_4 : ∀ I J g, Xc1_3_5_4 I J g = Xcc1_3_5_4 I J g := by
  decide +kernel

theorem hYtabc1_3_5_4 : ∀ I J g, Yc1_3_5_4 I J g = Ycc1_3_5_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc1_3_5_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_4 TL1_3_5 YLc1_3_5_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_3_5_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_5 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_5 : ∀ I J g, Xc1_3_5_5 I J g = Xcc1_3_5_5 I J g := by
  decide +kernel

theorem hYtabc1_3_5_5 : ∀ I J g, Yc1_3_5_5 I J g = Ycc1_3_5_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_3_5_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_5 TL1_3_5 YLc1_3_5_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_3_5_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]]]

noncomputable def Xcc1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_6 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_6 : ∀ I J g, Xc1_3_5_6 I J g = Xcc1_3_5_6 I J g := by
  decide +kernel

theorem hYtabc1_3_5_6 : ∀ I J g, Yc1_3_5_6 I J g = Ycc1_3_5_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_3_5_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_6 TL1_3_5 YLc1_3_5_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_5 (fuseRow (3 : ZMod 8) (5 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ro (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) ee) (fuseCol (3 : ZMod 8) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
      * fuseZ_1_0 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 5) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 I) (ri (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 5) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I)
          * realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_5 (fuseRow ((1 : ZMod 8) + 3) (5 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (5 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_3_5_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_3_5_7 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_5_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_5_7 : (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 5).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_5_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_5_7 : ∀ I J g, Xc1_3_5_7 I J g = Xcc1_3_5_7 I J g := by
  decide +kernel

theorem hYtabc1_3_5_7 : ∀ I J g, Yc1_3_5_7 I J g = Ycc1_3_5_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc1_3_5_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xc1_3_5_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hfuseZ_3_5 hfuseZ_1_0 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Xcc1_3_5_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_5_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Yc1_3_5_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hfuseZ_4_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 5)) Ycc1_3_5_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 5).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 5).2)) (realRepBasis ((1 : ZMod 8) + 3 + 5)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_5_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 5) (realGauge.gaugeSizeL 1 3 5).1 (realGauge.gaugeSizeL 1 3 5).2 ((sgn (realRepBasisParity (5 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_3_5_7 TL1_3_5 YLc1_3_5_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_3_5 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_3_5
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_3_5_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_3_5 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_5
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_3_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_3_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_3_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_3_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_3_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_3_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_3_5_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_3_5 (i : Fin (realRepDim (5 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i)) * T1_3_5
      = ((sgn (realRepBasisParity (5 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_3_5 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) (realRepBasis (5 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_3_5_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_3_5_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_3_5_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_3_5_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_3_5_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_3_5_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_3_5_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_3_5_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_3_5_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 T1_3_5 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 hT1_3_5 hAint1_3_5 hBint1_3_5 hCint1_3_5

theorem gtOfT1_3_5_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 T1_3_5 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) hsz1_3_5 T1_3_5_ne_zero

theorem gInterSpace1_3_5_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_3_5_mem_gInterSpace, gtOfT1_3_5_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_3_5 : gParity ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (5 : ZMod 8) gInterSpace1_3_5_ne_bot).symm

end Triple_1_3_5

/-! ### The triple `(1,3,7)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_3 = 8`, certgen parity `1`; the transported connector literal. -/
section Triple_1_3_7
open Module
theorem hsz1_3_7 : realGauge.gaugeSizeR 1 3 7 = realGauge.gaugeSizeL 1 3 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 8`). -/
def TL1_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc1_3_7 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet TL1_3_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T1_3_7 : ((realGauge.D ((1 : ZMod 8) + 3 + 7)).matrixSuper
    (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Tc1_3_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_3_7 : T1_3_7 ∈ ((realGauge.D ((1 : ZMod 8) + 3 + 7)).matrixSuper
    (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 3 + 7) Tc1_3_7 1 (by decide)

theorem T1_3_7_ne_zero : T1_3_7 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 3 + 7) Tc1_3_7 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨7, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_7_0 : ∀ I J g, Xa1_3_7_0 I J g = Xca1_3_7_0 I J g := by
  decide +kernel

theorem hYtaba1_3_7_0 : ∀ I J g, Ya1_3_7_0 I J g = Yca1_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_3_7_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xa1_3_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xca1_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ya1_3_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yca1_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_3_7_0 TL1_3_7 YLa1_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) = (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa1_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa1_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_3_7_1 : ∀ I J g, Xa1_3_7_1 I J g = Xca1_3_7_1 I J g := by
  decide +kernel

theorem hYtaba1_3_7_1 : ∀ I J g, Ya1_3_7_1 I J g = Yca1_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta1_3_7_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xa1_3_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xca1_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ya1_3_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yca1_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_3_7_1 TL1_3_7 YLa1_3_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_0 : ∀ I J g, Xb1_3_7_0 I J g = Xcb1_3_7_0 I J g := by
  decide +kernel

theorem hYtabb1_3_7_0 : ∀ I J g, Yb1_3_7_0 I J g = Ycb1_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_3_7_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_0 TL1_3_7 YLb1_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_1 : ∀ I J g, Xb1_3_7_1 I J g = Xcb1_3_7_1 I J g := by
  decide +kernel

theorem hYtabb1_3_7_1 : ∀ I J g, Yb1_3_7_1 I J g = Ycb1_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb1_3_7_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_1 TL1_3_7 YLb1_3_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_3_7_2 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_3_7_2 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]],
   [[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_2 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_2 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_2 : ∀ I J g, Xb1_3_7_2 I J g = Xcb1_3_7_2 I J g := by
  decide +kernel

theorem hYtabb1_3_7_2 : ∀ I J g, Yb1_3_7_2 I J g = Ycb1_3_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb1_3_7_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_2 TL1_3_7 YLb1_3_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_3_7_3 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_3_7_3 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_3_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_3_7_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcb1_3_7_3 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_3 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_3 : ∀ I J g, Xb1_3_7_3 I J g = Xcb1_3_7_3 I J g := by
  decide +kernel

theorem hYtabb1_3_7_3 : ∀ I J g, Yb1_3_7_3 I J g = Ycb1_3_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_3_7_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_3 TL1_3_7 YLb1_3_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb1_3_7_4 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb1_3_7_4 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb1_3_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb1_3_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_4 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_4 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_4 : ∀ I J g, Xb1_3_7_4 I J g = Xcb1_3_7_4 I J g := by
  decide +kernel

theorem hYtabb1_3_7_4 : ∀ I J g, Yb1_3_7_4 I J g = Ycb1_3_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb1_3_7_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_4 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_4 TL1_3_7 YLb1_3_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb1_3_7_5 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb1_3_7_5 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb1_3_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb1_3_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcb1_3_7_5 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_5 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_5 : ∀ I J g, Xb1_3_7_5 I J g = Xcb1_3_7_5 I J g := by
  decide +kernel

theorem hYtabb1_3_7_5 : ∀ I J g, Yb1_3_7_5 I J g = Ycb1_3_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb1_3_7_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_5 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_5 TL1_3_7 YLb1_3_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb1_3_7_6 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb1_3_7_6 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb1_3_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb1_3_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_6 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_6 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_6 : ∀ I J g, Xb1_3_7_6 I J g = Xcb1_3_7_6 I J g := by
  decide +kernel

theorem hYtabb1_3_7_6 : ∀ I J g, Yb1_3_7_6 I J g = Ycb1_3_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb1_3_7_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_6 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_6 TL1_3_7 YLb1_3_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb1_3_7_7 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb1_3_7_7 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_3 (fuseRow (1 : ZMod 8) (3 : ZMod 8) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb1_3_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb1_3_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_3_7_7 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb1_3_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_3_7_7 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb1_3_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_3_7_7 : ∀ I J g, Xb1_3_7_7 I J g = Xcb1_3_7_7 I J g := by
  decide +kernel

theorem hYtabb1_3_7_7 : ∀ I J g, Yb1_3_7_7 I J g = Ycb1_3_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb1_3_7_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xb1_3_7_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcb1_3_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_3_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yb1_3_7_7 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_1_3 hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycb1_3_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_3_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_3_7_7 TL1_3_7 YLb1_3_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_7_0 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_7_0 : ∀ I J g, Xc1_3_7_0 I J g = Xcc1_3_7_0 I J g := by
  decide +kernel

theorem hYtabc1_3_7_0 : ∀ I J g, Yc1_3_7_0 I J g = Ycc1_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_3_7_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xc1_3_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcc1_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yc1_3_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycc1_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_7_0 TL1_3_7 YLc1_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ro (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_1_2 (fuseRow (1 : ZMod 8) ((3 : ZMod 8) + 7) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 I) (ri (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 J) g) (fuseCol (1 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) = (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (3 : ZMod 8)).1 (realSize (1 : ZMod 8) (3 : ZMod 8)).2 (lo (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_4_7 (fuseRow ((1 : ZMod 8) + 3) (7 : ZMod 8) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 3) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcc1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc1_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_3_7_1 : (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2) → Fin (realRepDim ((1 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc1_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 8 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_3_7_1 : ∀ I J g, Xc1_3_7_1 I J g = Xcc1_3_7_1 I J g := by
  decide +kernel

theorem hYtabc1_3_7_1 : ∀ I J g, Yc1_3_7_1 I J g = Ycc1_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc1_3_7_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T1_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xc1_3_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hfuseZ_3_7 hfuseZ_1_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Xcc1_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Yc1_3_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_4_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 3 + 7)) Ycc1_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 1 3 7).2)) (realRepBasis ((1 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 1 3 7).1 (realGauge.gaugeSizeL 1 3 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_3_7_1 TL1_3_7 YLc1_3_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_3_7 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_3_7
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_3_7_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_3_7 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_3_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_3_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_3_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb1_3_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb1_3_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb1_3_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb1_3_7_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_3_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T1_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_3_7 * (realGauge.gaugeRouteL (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_3_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_3_7_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 T1_3_7 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 hT1_3_7 hAint1_3_7 hBint1_3_7 hCint1_3_7

theorem gtOfT1_3_7_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 T1_3_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz1_3_7 T1_3_7_ne_zero

theorem gInterSpace1_3_7_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_3_7_mem_gInterSpace, gtOfT1_3_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_3_7 : gParity ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) gInterSpace1_3_7_ne_bot).symm

end Triple_1_3_7

/-! ### The triple `(1,4,0)`

`gaugeSizeL = gaugeSizeR = (1,0)`, `dim D_5 = 8`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_1_4_0
open Module
theorem hsz1_4_0 : realGauge.gaugeSizeR 1 4 0 = realGauge.gaugeSizeL 1 4 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`1 x 1 x 8`). -/
def TL1_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 0`. -/
noncomputable def Tc1_4_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet TL1_4_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_5`. -/
noncomputable def T1_4_0 : ((realGauge.D ((1 : ZMod 8) + 4 + 0)).matrixSuper
    (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Tc1_4_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_4_0 : T1_4_0 ∈ ((realGauge.D ((1 : ZMod 8) + 4 + 0)).matrixSuper
    (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 4 + 0) Tc1_4_0 0 (by decide)

theorem T1_4_0_ne_zero : T1_4_0 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 4 + 0) Tc1_4_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_0_0 : ∀ I J g, Xa1_4_0_0 I J g = Xca1_4_0_0 I J g := by
  decide +kernel

theorem hYtaba1_4_0_0 : ∀ I J g, Ya1_4_0_0 I J g = Yca1_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_4_0_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xa1_4_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xca1_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ya1_4_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yca1_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_4_0_0 TL1_4_0 YLa1_4_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1]]]

noncomputable def Xca1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_0_1 : ∀ I J g, Xa1_4_0_1 I J g = Xca1_4_0_1 I J g := by
  decide +kernel

theorem hYtaba1_4_0_1 : ∀ I J g, Ya1_4_0_1 I J g = Yca1_4_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_4_0_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xa1_4_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_1_4 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xca1_4_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ya1_4_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yca1_4_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_4_0_1 TL1_4_0 YLa1_4_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_0_0 : ∀ I J g, Xb1_4_0_0 I J g = Xcb1_4_0_0 I J g := by
  decide +kernel

theorem hYtabb1_4_0_0 : ∀ I J g, Yb1_4_0_0 I J g = Ycb1_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_4_0_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xb1_4_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_4_0 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xcb1_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yb1_4_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ycb1_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_0_0 TL1_4_0 YLb1_4_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcb1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_0_1 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_0_1 : ∀ I J g, Xb1_4_0_1 I J g = Xcb1_4_0_1 I J g := by
  decide +kernel

theorem hYtabb1_4_0_1 : ∀ I J g, Yb1_4_0_1 I J g = Ycb1_4_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_4_0_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xb1_4_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_4_0 hfuseZ_1_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xcb1_4_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yb1_4_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ycb1_4_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_0_1 TL1_4_0 YLb1_4_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_4_0_2 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_4_0_2 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 1, 0]]]

noncomputable def Xcb1_4_0_2 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_0_2 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_0_2 : ∀ I J g, Xb1_4_0_2 I J g = Xcb1_4_0_2 I J g := by
  decide +kernel

theorem hYtabb1_4_0_2 : ∀ I J g, Yb1_4_0_2 I J g = Ycb1_4_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_4_0_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xb1_4_0_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_4_0 hfuseZ_1_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xcb1_4_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yb1_4_0_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ycb1_4_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_0_2 TL1_4_0 YLb1_4_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_4_0_3 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_4_0_3 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 1, 0, 0]]]

noncomputable def Xcb1_4_0_3 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_0_3 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_0_3 : ∀ I J g, Xb1_4_0_3 I J g = Xcb1_4_0_3 I J g := by
  decide +kernel

theorem hYtabb1_4_0_3 : ∀ I J g, Yb1_4_0_3 I J g = Ycb1_4_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_4_0_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xb1_4_0_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_4_0 hfuseZ_1_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xcb1_4_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yb1_4_0_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_1_4 hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ycb1_4_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_0_3 TL1_4_0 YLb1_4_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ro (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_1_4 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 0) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 I) (ri (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_0 (fuseRow ((1 : ZMod 8) + 4) (0 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_0_0 : (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `1² · 8 = 8` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_0_0 : ∀ I J g, Xc1_4_0_0 I J g = Xcc1_4_0_0 I J g := by
  decide +kernel

theorem hYtabc1_4_0_0 : ∀ I J g, Yc1_4_0_0 I J g = Ycc1_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_4_0_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T1_4_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xc1_4_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hfuseZ_4_0 hfuseZ_1_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Xcc1_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Yc1_4_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_5_0 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 0)) Ycc1_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 0).2)) (realRepBasis ((1 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 1 4 0).1 (realGauge.gaugeSizeL 1 4 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_0_0 TL1_4_0 YLc1_4_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_4_0 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_4_0
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_4_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_4_0_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_4_0 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_4_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_4_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_4_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_4_0_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_4_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T1_4_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_0 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc1_4_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_4_0_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 T1_4_0 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 hT1_4_0 hAint1_4_0 hBint1_4_0 hCint1_4_0

theorem gtOfT1_4_0_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 T1_4_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz1_4_0 T1_4_0_ne_zero

theorem gInterSpace1_4_0_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_4_0_mem_gInterSpace, gtOfT1_4_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_4_0 : gParity ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) gInterSpace1_4_0_ne_bot).symm

end Triple_1_4_0

/-! ### The triple `(1,4,1)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_6 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_1_4_1
open Module
theorem hsz1_4_1 : realGauge.gaugeSizeR 1 4 1 = realGauge.gaugeSizeL 1 4 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 4`). -/
def TL1_4_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, -1]],
   [[-1, 0, 0, -1], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc1_4_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet TL1_4_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T1_4_1 : ((realGauge.D ((1 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Tc1_4_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_4_1 : T1_4_1 ∈ ((realGauge.D ((1 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 4 + 1) Tc1_4_1 1 (by decide)

theorem T1_4_1_ne_zero : T1_4_1 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 4 + 1) Tc1_4_1 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_1_0 : ∀ I J g, Xa1_4_1_0 I J g = Xca1_4_1_0 I J g := by
  decide +kernel

theorem hYtaba1_4_1_0 : ∀ I J g, Ya1_4_1_0 I J g = Yca1_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_4_1_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xa1_4_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xca1_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ya1_4_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yca1_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_4_1_0 TL1_4_1 YLa1_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 1], [0, 0, 0, 0]]]

noncomputable def Xca1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_1_1 : ∀ I J g, Xa1_4_1_1 I J g = Xca1_4_1_1 I J g := by
  decide +kernel

theorem hYtaba1_4_1_1 : ∀ I J g, Ya1_4_1_1 I J g = Yca1_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta1_4_1_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xa1_4_1_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_1_5 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xca1_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ya1_4_1_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yca1_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa1_4_1_1 TL1_4_1 YLa1_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_1_0 : ∀ I J g, Xb1_4_1_0 I J g = Xcb1_4_1_0 I J g := by
  decide +kernel

theorem hYtabb1_4_1_0 : ∀ I J g, Yb1_4_1_0 I J g = Ycb1_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_4_1_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xb1_4_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcb1_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yb1_4_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycb1_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_1_0 TL1_4_1 YLb1_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcb1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_1_1 : ∀ I J g, Xb1_4_1_1 I J g = Xcb1_4_1_1 I J g := by
  decide +kernel

theorem hYtabb1_4_1_1 : ∀ I J g, Yb1_4_1_1 I J g = Ycb1_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_4_1_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xb1_4_1_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcb1_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yb1_4_1_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycb1_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_1_1 TL1_4_1 YLb1_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_4_1_2 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_4_1_2 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_4_1_2 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_1_2 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_1_2 : ∀ I J g, Xb1_4_1_2 I J g = Xcb1_4_1_2 I J g := by
  decide +kernel

theorem hYtabb1_4_1_2 : ∀ I J g, Yb1_4_1_2 I J g = Ycb1_4_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_4_1_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xb1_4_1_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcb1_4_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yb1_4_1_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycb1_4_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_1_2 TL1_4_1 YLb1_4_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_4_1_3 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_4_1_3 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb1_4_1_3 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_1_3 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_1_3 : ∀ I J g, Xb1_4_1_3 I J g = Xcb1_4_1_3 I J g := by
  decide +kernel

theorem hYtabb1_4_1_3 : ∀ I J g, Yb1_4_1_3 I J g = Ycb1_4_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_4_1_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xb1_4_1_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcb1_4_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yb1_4_1_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_1_4 hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycb1_4_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb1_4_1_3 TL1_4_1 YLb1_4_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_1_0 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_1_0 : ∀ I J g, Xc1_4_1_0 I J g = Xcc1_4_1_0 I J g := by
  decide +kernel

theorem hYtabc1_4_1_0 : ∀ I J g, Yc1_4_1_0 I J g = Ycc1_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_4_1_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xc1_4_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcc1_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yc1_4_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycc1_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_1_0 TL1_4_1 YLc1_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ro (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_1_5 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 1) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 I) (ri (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_1 (fuseRow ((1 : ZMod 8) + 4) (1 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 1], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_1_1 : (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_1_1 : ∀ I J g, Xc1_4_1_1 I J g = Xcc1_4_1_1 I J g := by
  decide +kernel

theorem hYtabc1_4_1_1 : ∀ I J g, Yc1_4_1_1 I J g = Ycc1_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc1_4_1_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xc1_4_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hfuseZ_4_1 hfuseZ_1_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Xcc1_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Yc1_4_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_5_1 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 1)) Ycc1_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 1).2)) (realRepBasis ((1 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 1 4 1).1 (realGauge.gaugeSizeL 1 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc1_4_1_1 TL1_4_1 YLc1_4_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_4_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_4_1_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_4_1 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_4_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_4_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_4_1_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_4_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T1_4_1 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_4_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_4_1_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 T1_4_1 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 hT1_4_1 hAint1_4_1 hBint1_4_1 hCint1_4_1

theorem gtOfT1_4_1_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 T1_4_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz1_4_1 T1_4_1_ne_zero

theorem gInterSpace1_4_1_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_4_1_mem_gInterSpace, gtOfT1_4_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_4_1 : gParity ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) gInterSpace1_4_1_ne_bot).symm

end Triple_1_4_1

/-! ### The triple `(1,4,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `0`; the transported connector literal. -/
section Triple_1_4_3
open Module
theorem hsz1_4_3 : realGauge.gaugeSizeR 1 4 3 = realGauge.gaugeSizeL 1 4 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL1_4_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc1_4_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet TL1_4_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T1_4_3 : ((realGauge.D ((1 : ZMod 8) + 4 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2).carrier :=
  matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Tc1_4_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT1_4_3 : T1_4_3 ∈ ((realGauge.D ((1 : ZMod 8) + 4 + 3)).matrixSuper
    (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((1 : ZMod 8) + 4 + 3) Tc1_4_3 0 (by decide)

theorem T1_4_3_ne_zero : T1_4_3 ≠ 0 :=
  matOfCoeff_ne_zero ((1 : ZMod 8) + 4 + 3) Tc1_4_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨2, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_3_0 : ∀ I J g, Xa1_4_3_0 I J g = Xca1_4_3_0 I J g := by
  decide +kernel

theorem hYtaba1_4_3_0 : ∀ I J g, Ya1_4_3_0 I J g = Yca1_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta1_4_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xa1_4_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xca1_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ya1_4_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yca1_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_4_3_0 TL1_4_3 YLa1_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) = (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa1_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa1_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba1_4_3_1 : ∀ I J g, Xa1_4_3_1 I J g = Xca1_4_3_1 I J g := by
  decide +kernel

theorem hYtaba1_4_3_1 : ∀ I J g, Ya1_4_3_1 I J g = Yca1_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta1_4_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xa1_4_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xca1_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba1_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ya1_4_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yca1_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba1_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa1_4_3_1 TL1_4_3 YLa1_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_3_0 : ∀ I J g, Xb1_4_3_0 I J g = Xcb1_4_3_0 I J g := by
  decide +kernel

theorem hYtabb1_4_3_0 : ∀ I J g, Yb1_4_3_0 I J g = Ycb1_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb1_4_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xb1_4_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcb1_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yb1_4_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycb1_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_3_0 TL1_4_3 YLb1_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_3_1 : ∀ I J g, Xb1_4_3_1 I J g = Xcb1_4_3_1 I J g := by
  decide +kernel

theorem hYtabb1_4_3_1 : ∀ I J g, Yb1_4_3_1 I J g = Ycb1_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb1_4_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xb1_4_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcb1_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yb1_4_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycb1_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_3_1 TL1_4_3 YLb1_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb1_4_3_2 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb1_4_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_3_2 : ∀ I J g, Xb1_4_3_2 I J g = Xcb1_4_3_2 I J g := by
  decide +kernel

theorem hYtabb1_4_3_2 : ∀ I J g, Yb1_4_3_2 I J g = Ycb1_4_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb1_4_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xb1_4_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcb1_4_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yb1_4_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycb1_4_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_3_2 TL1_4_3 YLb1_4_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_1_4 (fuseRow (1 : ZMod 8) (4 : ZMod 8) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (1 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb1_4_3_3 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb1_4_3_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcb1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb1_4_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb1_4_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb1_4_3_3 : ∀ I J g, Xb1_4_3_3 I J g = Xcb1_4_3_3 I J g := by
  decide +kernel

theorem hYtabb1_4_3_3 : ∀ I J g, Yb1_4_3_3 I J g = Ycb1_4_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb1_4_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xb1_4_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcb1_4_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb1_4_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yb1_4_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_1_4 hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycb1_4_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb1_4_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb1_4_3_3 TL1_4_3 YLb1_4_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc1_4_3_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_0 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_0 : ∀ I J g, Xc1_4_3_0 I J g = Xcc1_4_3_0 I J g := by
  decide +kernel

theorem hYtabc1_4_3_0 : ∀ I J g, Yc1_4_3_0 I J g = Ycc1_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc1_4_3_0 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_0 TL1_4_3 YLc1_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc1_4_3_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_1 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_1 : ∀ I J g, Xc1_4_3_1 I J g = Xcc1_4_3_1 I J g := by
  decide +kernel

theorem hYtabc1_4_3_1 : ∀ I J g, Yc1_4_3_1 I J g = Ycc1_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc1_4_3_1 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_1 TL1_4_3 YLc1_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc1_4_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc1_4_3_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

noncomputable def Xcc1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_2 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_2 : ∀ I J g, Xc1_4_3_2 I J g = Xcc1_4_3_2 I J g := by
  decide +kernel

theorem hYtabc1_4_3_2 : ∀ I J g, Yc1_4_3_2 I J g = Ycc1_4_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc1_4_3_2 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_2 TL1_4_3 YLc1_4_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc1_4_3_3 : List (List (List ℤ)) :=
  [[[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc1_4_3_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcc1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_3 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_3 : ∀ I J g, Xc1_4_3_3 I J g = Xcc1_4_3_3 I J g := by
  decide +kernel

theorem hYtabc1_4_3_3 : ∀ I J g, Yc1_4_3_3 I J g = Ycc1_4_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc1_4_3_3 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_3 TL1_4_3 YLc1_4_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc1_4_3_4 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc1_4_3_4 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc1_4_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc1_4_3_4 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc1_4_3_4 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_4 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_4 : ∀ I J g, Xc1_4_3_4 I J g = Xcc1_4_3_4 I J g := by
  decide +kernel

theorem hYtabc1_4_3_4 : ∀ I J g, Yc1_4_3_4 I J g = Ycc1_4_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc1_4_3_4 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_4 TL1_4_3 YLc1_4_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc1_4_3_5 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc1_4_3_5 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc1_4_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc1_4_3_5 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcc1_4_3_5 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_5 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_5 : ∀ I J g, Xc1_4_3_5 I J g = Xcc1_4_3_5 I J g := by
  decide +kernel

theorem hYtabc1_4_3_5 : ∀ I J g, Yc1_4_3_5 I J g = Ycc1_4_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc1_4_3_5 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_5 TL1_4_3 YLc1_4_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc1_4_3_6 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc1_4_3_6 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc1_4_3_6 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc1_4_3_6 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcc1_4_3_6 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_6 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_6 : ∀ I J g, Xc1_4_3_6 I J g = Xcc1_4_3_6 I J g := by
  decide +kernel

theorem hYtabc1_4_3_6 : ∀ I J g, Yc1_4_3_6 I J g = Ycc1_4_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc1_4_3_6 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_6 TL1_4_3 YLc1_4_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc1_4_3_7 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ro (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_1_7 (fuseRow (1 : ZMod 8) ((4 : ZMod 8) + 3) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 I) (ri (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 J) g) (fuseCol (1 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc1_4_3_7 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (1 : ZMod 8) (4 : ZMod 8)).1 (realSize (1 : ZMod 8) (4 : ZMod 8)).2 (lo (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_3 (fuseRow ((1 : ZMod 8) + 4) (3 : ZMod 8) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((1 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc1_4_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc1_4_3_7 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xcc1_4_3_7 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc1_4_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc1_4_3_7 : (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2) → Fin (realRepDim ((1 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc1_4_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc1_4_3_7 : ∀ I J g, Xc1_4_3_7 I J g = Xcc1_4_3_7 I J g := by
  decide +kernel

theorem hYtabc1_4_3_7 : ∀ I J g, Yc1_4_3_7 I J g = Ycc1_4_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc1_4_3_7 :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xc1_4_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hfuseZ_4_3 hfuseZ_1_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Xcc1_4_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc1_4_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Yc1_4_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_5_3 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((1 : ZMod 8) + 4 + 3)) Ycc1_4_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 1 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 1 4 3).2)) (realRepBasis ((1 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc1_4_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((1 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 1 4 3).1 (realGauge.gaugeSizeL 1 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc1_4_3_7 TL1_4_3 YLc1_4_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint1_4_3 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T1_4_3
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hinta1_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hinta1_4_3_1

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint1_4_3 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T1_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb1_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb1_4_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb1_4_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb1_4_3_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint1_4_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T1_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T1_4_3 * (realGauge.gaugeRouteL (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc1_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc1_4_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc1_4_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc1_4_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc1_4_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc1_4_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc1_4_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc1_4_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT1_4_3_mem_gInterSpace :
    gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 T1_4_3 ∈ gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 hT1_4_3 hAint1_4_3 hBint1_4_3 hCint1_4_3

theorem gtOfT1_4_3_ne_zero : gtOfT ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 T1_4_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz1_4_3 T1_4_3_ne_zero

theorem gInterSpace1_4_3_ne_bot : gInterSpace ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT1_4_3_mem_gInterSpace, gtOfT1_4_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_1_4_3 : gParity ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (1 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) gInterSpace1_4_3_ne_bot).symm

end Triple_1_4_3

end G1_2
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_3_3
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_3_4
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_3_5
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_3_7
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_4_0
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_4_1
#print axioms Superfusion.GaugeChi.TripleCerts.G1_2.gParity_1_4_3
