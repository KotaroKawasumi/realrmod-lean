/-
Superfusion / GaugeChi / TripleCerts / G2_8

**GENERATED FILE — do not edit.**  Regenerate with

    python3 scripts/certgen/gen_triple_certs.py \
        --triples 2,3,6 2,3,7 2,4,0 2,4,1 2,4,2 2,4,3 \
        --module G2_8 \
        --out Superfusion/GaugeChi/TripleCerts/G2_8.lean

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

Triples (6): (2,3,6), (2,3,7), (2,4,0), (2,4,1), (2,4,2), (2,4,3).
Unit-slot triples (`a = 0` or `b = 0` or `c = 0`) in this batch: (2,4,0).
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
namespace G2_8

open Module

/-! ### The fusion shadows this batch uses (19 of the 64)

They are declared at the enclosing `TripleCerts` namespace by
`TripleCerts/FuseShadows.lean`, so the short names below resolve
unqualified and no `open` is needed:

  `fuseZ_2_1`, `fuseZ_2_2`, `fuseZ_2_3`, `fuseZ_2_4`, `fuseZ_2_5`, `fuseZ_2_6`, `fuseZ_2_7`, `fuseZ_3_6`, `fuseZ_3_7`, `fuseZ_4_0`, `fuseZ_4_1`, `fuseZ_4_2`, `fuseZ_4_3`, `fuseZ_5_6`, `fuseZ_5_7`, `fuseZ_6_0`, `fuseZ_6_1`, `fuseZ_6_2`, `fuseZ_6_3`. -/

/-! ### The triple `(2,3,6)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_3 = 8`, certgen parity `1`; the transported connector literal. -/
section Triple_2_3_6
open Module
theorem hsz2_3_6 : realGauge.gaugeSizeR 2 3 6 = realGauge.gaugeSizeL 2 3 6 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 8`). -/
def TL2_3_6 : List (List (List ℤ)) :=
  [[[0, -1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, -1], [1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, -1, 0]],
   [[0, -1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 1], [-1, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, -1, 0]],
   [[0, 0, 0, 0, 0, -1, -1, 0], [-1, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, -1], [0, 1, -1, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, -1, 0], [1, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 1], [0, 1, -1, 0, 0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc2_3_6 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet TL2_3_6 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_3`. -/
noncomputable def T2_3_6 : ((realGauge.D ((2 : ZMod 8) + 3 + 6)).matrixSuper
    (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Tc2_3_6

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_3_6 : T2_3_6 ∈ ((realGauge.D ((2 : ZMod 8) + 3 + 6)).matrixSuper
    (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 3 + 6) Tc2_3_6 1 (by decide)

theorem T2_3_6_ne_zero : T2_3_6 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 3 + 6) Tc2_3_6 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨1, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_6_0 : ∀ I J g, Xa2_3_6_0 I J g = Xca2_3_6_0 I J g := by
  decide +kernel

theorem hYtaba2_3_6_0 : ∀ I J g, Ya2_3_6_0 I J g = Yca2_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_3_6_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xa2_3_6_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xca2_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ya2_3_6_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yca2_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_6_0 TL2_3_6 YLa2_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_6_1 : ∀ I J g, Xa2_3_6_1 I J g = Xca2_3_6_1 I J g := by
  decide +kernel

theorem hYtaba2_3_6_1 : ∀ I J g, Ya2_3_6_1 I J g = Yca2_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta2_3_6_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xa2_3_6_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_2_1 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xca2_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ya2_3_6_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yca2_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_6_1 TL2_3_6 YLa2_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xca2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_6_2 : ∀ I J g, Xa2_3_6_2 I J g = Xca2_3_6_2 I J g := by
  decide +kernel

theorem hYtaba2_3_6_2 : ∀ I J g, Ya2_3_6_2 I J g = Yca2_3_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta2_3_6_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xa2_3_6_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_2_1 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xca2_3_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ya2_3_6_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yca2_3_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_6_2 TL2_3_6 YLa2_3_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (6 : ZMod 8)).1 (realSize (3 : ZMod 8) (6 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0]]]

noncomputable def Xca2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_6_3 : ∀ I J g, Xa2_3_6_3 I J g = Xca2_3_6_3 I J g := by
  decide +kernel

theorem hYtaba2_3_6_3 : ∀ I J g, Ya2_3_6_3 I J g = Yca2_3_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_3_6_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xa2_3_6_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_2_1 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xca2_3_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ya2_3_6_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yca2_3_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_6_3 TL2_3_6 YLa2_3_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_0 : ∀ I J g, Xb2_3_6_0 I J g = Xcb2_3_6_0 I J g := by
  decide +kernel

theorem hYtabb2_3_6_0 : ∀ I J g, Yb2_3_6_0 I J g = Ycb2_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_3_6_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_0 TL2_3_6 YLb2_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_1 : ∀ I J g, Xb2_3_6_1 I J g = Xcb2_3_6_1 I J g := by
  decide +kernel

theorem hYtabb2_3_6_1 : ∀ I J g, Yb2_3_6_1 I J g = Ycb2_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb2_3_6_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_1 TL2_3_6 YLb2_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_2 : ∀ I J g, Xb2_3_6_2 I J g = Xcb2_3_6_2 I J g := by
  decide +kernel

theorem hYtabb2_3_6_2 : ∀ I J g, Yb2_3_6_2 I J g = Ycb2_3_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb2_3_6_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_2 TL2_3_6 YLb2_3_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_3 : ∀ I J g, Xb2_3_6_3 I J g = Xcb2_3_6_3 I J g := by
  decide +kernel

theorem hYtabb2_3_6_3 : ∀ I J g, Yb2_3_6_3 I J g = Ycb2_3_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_3_6_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_3 TL2_3_6 YLb2_3_6_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb2_3_6_4 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb2_3_6_4 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb2_3_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb2_3_6_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_4 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_4 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_4 : ∀ I J g, Xb2_3_6_4 I J g = Xcb2_3_6_4 I J g := by
  decide +kernel

theorem hYtabb2_3_6_4 : ∀ I J g, Yb2_3_6_4 I J g = Ycb2_3_6_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb2_3_6_4 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_4 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_4 TL2_3_6 YLb2_3_6_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb2_3_6_5 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb2_3_6_5 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb2_3_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb2_3_6_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_5 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_5 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_5 : ∀ I J g, Xb2_3_6_5 I J g = Xcb2_3_6_5 I J g := by
  decide +kernel

theorem hYtabb2_3_6_5 : ∀ I J g, Yb2_3_6_5 I J g = Ycb2_3_6_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb2_3_6_5 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_5 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_5 TL2_3_6 YLb2_3_6_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb2_3_6_6 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb2_3_6_6 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb2_3_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb2_3_6_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_6 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_6 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_6 : ∀ I J g, Xb2_3_6_6 I J g = Xcb2_3_6_6 I J g := by
  decide +kernel

theorem hYtabb2_3_6_6 : ∀ I J g, Yb2_3_6_6 I J g = Ycb2_3_6_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb2_3_6_6 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_6 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_6 TL2_3_6 YLb2_3_6_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb2_3_6_7 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb2_3_6_7 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb2_3_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb2_3_6_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
   [[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcb2_3_6_7 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_6_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_6_7 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_6_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_6_7 : ∀ I J g, Xb2_3_6_7 I J g = Xcb2_3_6_7 I J g := by
  decide +kernel

theorem hYtabb2_3_6_7 : ∀ I J g, Yb2_3_6_7 I J g = Ycb2_3_6_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb2_3_6_7 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xb2_3_6_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcb2_3_6_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_6_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yb2_3_6_7 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_2_3 hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycb2_3_6_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_6_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_6_7 TL2_3_6 YLb2_3_6_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_3_6_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_6_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_6_0 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_6_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_6_0 : ∀ I J g, Xc2_3_6_0 I J g = Xcc2_3_6_0 I J g := by
  decide +kernel

theorem hYtabc2_3_6_0 : ∀ I J g, Yc2_3_6_0 I J g = Ycc2_3_6_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_3_6_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xc2_3_6_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcc2_3_6_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_6_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yc2_3_6_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycc2_3_6_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_6_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_6_0 TL2_3_6 YLc2_3_6_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc2_3_6_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0]],
   [[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_6_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_6_1 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_6_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_6_1 : ∀ I J g, Xc2_3_6_1 I J g = Xcc2_3_6_1 I J g := by
  decide +kernel

theorem hYtabc2_3_6_1 : ∀ I J g, Yc2_3_6_1 I J g = Ycc2_3_6_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc2_3_6_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xc2_3_6_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcc2_3_6_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_6_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yc2_3_6_1 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycc2_3_6_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_6_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_6_1 TL2_3_6 YLc2_3_6_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc2_3_6_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, -1]]]

noncomputable def Xcc2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_6_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_6_2 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_6_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_6_2 : ∀ I J g, Xc2_3_6_2 I J g = Xcc2_3_6_2 I J g := by
  decide +kernel

theorem hYtabc2_3_6_2 : ∀ I J g, Yc2_3_6_2 I J g = Ycc2_3_6_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintc2_3_6_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xc2_3_6_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcc2_3_6_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_6_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yc2_3_6_2 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycc2_3_6_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_6_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_6_2 TL2_3_6 YLc2_3_6_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_6 (fuseRow (3 : ZMod 8) (6 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ro (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) ee) (fuseCol (3 : ZMod 8) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
      * fuseZ_2_1 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 6) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 I) (ri (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 6) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I)
          * realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_6 (fuseRow ((2 : ZMod 8) + 3) (6 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (6 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc2_3_6_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0]],
   [[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]]

noncomputable def Xcc2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_6_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_6_3 : (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 6).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_6_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 8 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_6_3 : ∀ I J g, Xc2_3_6_3 I J g = Xcc2_3_6_3 I J g := by
  decide +kernel

theorem hYtabc2_3_6_3 : ∀ I J g, Yc2_3_6_3 I J g = Ycc2_3_6_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc2_3_6_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))) * T2_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xc2_3_6_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hfuseZ_3_6 hfuseZ_2_1 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Xcc2_3_6_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_6_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Yc2_3_6_3 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hfuseZ_5_6 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 6)) Ycc2_3_6_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 6).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 6).2)) (realRepBasis ((2 : ZMod 8) + 3 + 6)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_6_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 6) (realGauge.gaugeSizeL 2 3 6).1 (realGauge.gaugeSizeL 2 3 6).2 ((sgn (realRepBasisParity (6 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_6_3 TL2_3_6 YLc2_3_6_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_3_6 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_3_6
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_3_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_3_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_3_6_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_3_6 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T2_3_6
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_3_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_3_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_3_6_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb2_3_6_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb2_3_6_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb2_3_6_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb2_3_6_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_3_6 (i : Fin (realRepDim (6 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i)) * T2_3_6
      = ((sgn (realRepBasisParity (6 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_6 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) (realRepBasis (6 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h0]; exact hintc2_3_6_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h1]; exact hintc2_3_6_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h2]; exact hintc2_3_6_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) from Fin.ext h3]; exact hintc2_3_6_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_3_6_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 T2_3_6 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 hT2_3_6 hAint2_3_6 hBint2_3_6 hCint2_3_6

theorem gtOfT2_3_6_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 T2_3_6 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) hsz2_3_6 T2_3_6_ne_zero

theorem gInterSpace2_3_6_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_3_6_mem_gInterSpace, gtOfT2_3_6_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_3_6 : gParity ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (6 : ZMod 8) gInterSpace2_3_6_ne_bot).symm

end Triple_2_3_6

/-! ### The triple `(2,3,7)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_4 = 4`, certgen parity `1`; the transported connector literal. -/
section Triple_2_3_7
open Module
theorem hsz2_3_7 : realGauge.gaugeSizeR 2 3 7 = realGauge.gaugeSizeL 2 3 7 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 4`). -/
def TL2_3_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 1]],
   [[0, 0, 0, 0], [-1, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc2_3_7 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet TL2_3_7 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_4`. -/
noncomputable def T2_3_7 : ((realGauge.D ((2 : ZMod 8) + 3 + 7)).matrixSuper
    (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Tc2_3_7

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_3_7 : T2_3_7 ∈ ((realGauge.D ((2 : ZMod 8) + 3 + 7)).matrixSuper
    (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 3 + 7) Tc2_3_7 1 (by decide)

theorem T2_3_7_ne_zero : T2_3_7 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 3 + 7) Tc2_3_7 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_7_0 : ∀ I J g, Xa2_3_7_0 I J g = Xca2_3_7_0 I J g := by
  decide +kernel

theorem hYtaba2_3_7_0 : ∀ I J g, Ya2_3_7_0 I J g = Yca2_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_3_7_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xa2_3_7_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_2_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xca2_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ya2_3_7_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yca2_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_7_0 TL2_3_7 YLa2_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_7_1 : ∀ I J g, Xa2_3_7_1 I J g = Xca2_3_7_1 I J g := by
  decide +kernel

theorem hYtaba2_3_7_1 : ∀ I J g, Ya2_3_7_1 I J g = Yca2_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta2_3_7_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xa2_3_7_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_2_2 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xca2_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ya2_3_7_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yca2_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_7_1 TL2_3_7 YLa2_3_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_7_2 : ∀ I J g, Xa2_3_7_2 I J g = Xca2_3_7_2 I J g := by
  decide +kernel

theorem hYtaba2_3_7_2 : ∀ I J g, Ya2_3_7_2 I J g = Yca2_3_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta2_3_7_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xa2_3_7_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_2_2 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xca2_3_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ya2_3_7_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yca2_3_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_7_2 TL2_3_7 YLa2_3_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) = (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) then
      ((sgn (sumParity (realSize (3 : ZMod 8) (7 : ZMod 8)).1 (realSize (3 : ZMod 8) (7 : ZMod 8)).2 (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_3_7_3 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_3_7_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]]]

noncomputable def Xca2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLa2_3_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLa2_3_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_3_7_3 : ∀ I J g, Xa2_3_7_3 I J g = Xca2_3_7_3 I J g := by
  decide +kernel

theorem hYtaba2_3_7_3 : ∀ I J g, Ya2_3_7_3 I J g = Yca2_3_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_3_7_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xa2_3_7_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_2_2 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xca2_3_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_3_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ya2_3_7_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yca2_3_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_3_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_3_7_3 TL2_3_7 YLa2_3_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_0 : ∀ I J g, Xb2_3_7_0 I J g = Xcb2_3_7_0 I J g := by
  decide +kernel

theorem hYtabb2_3_7_0 : ∀ I J g, Yb2_3_7_0 I J g = Ycb2_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_3_7_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_0 TL2_3_7 YLb2_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_1 : ∀ I J g, Xb2_3_7_1 I J g = Xcb2_3_7_1 I J g := by
  decide +kernel

theorem hYtabb2_3_7_1 : ∀ I J g, Yb2_3_7_1 I J g = Ycb2_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintb2_3_7_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_1 TL2_3_7 YLb2_3_7_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_3_7_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_2 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_2 : ∀ I J g, Xb2_3_7_2 I J g = Xcb2_3_7_2 I J g := by
  decide +kernel

theorem hYtabb2_3_7_2 : ∀ I J g, Yb2_3_7_2 I J g = Ycb2_3_7_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `-1`). -/
theorem hintb2_3_7_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_2 TL2_3_7 YLb2_3_7_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_3_7_3 : List (List (List ℤ)) :=
  [[[0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_3_7_3 : List (List (List ℤ)) :=
  [[[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]]]

noncomputable def Xcb2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_3 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_3 : ∀ I J g, Xb2_3_7_3 I J g = Xcb2_3_7_3 I J g := by
  decide +kernel

theorem hYtabb2_3_7_3 : ∀ I J g, Yb2_3_7_3 I J g = Ycb2_3_7_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_3_7_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_3 TL2_3_7 YLb2_3_7_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Xb2_3_7_4 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `4`. -/
noncomputable def Yb2_3_7_4 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `4`, pre-tabulated. -/
def XLb2_3_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `4`, pre-tabulated. -/
def YLb2_3_7_4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_4 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_4 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_4 : ∀ I J g, Xb2_3_7_4 I J g = Xcb2_3_7_4 I J g := by
  decide +kernel

theorem hYtabb2_3_7_4 : ∀ I J g, Yb2_3_7_4 I J g = Ycb2_3_7_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `4`** (Koszul sign `-1`). -/
theorem hintb2_3_7_4 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_4 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_4 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_4 TL2_3_7 YLb2_3_7_4 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Xb2_3_7_5 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `5`. -/
noncomputable def Yb2_3_7_5 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `5`, pre-tabulated. -/
def XLb2_3_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `5`, pre-tabulated. -/
def YLb2_3_7_5 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_5 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_5 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_5 : ∀ I J g, Xb2_3_7_5 I J g = Xcb2_3_7_5 I J g := by
  decide +kernel

theorem hYtabb2_3_7_5 : ∀ I J g, Yb2_3_7_5 I J g = Ycb2_3_7_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintb2_3_7_5 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_5 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_5 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_5 TL2_3_7 YLb2_3_7_5 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Xb2_3_7_6 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `6`. -/
noncomputable def Yb2_3_7_6 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `6`, pre-tabulated. -/
def XLb2_3_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [-1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `6`, pre-tabulated. -/
def YLb2_3_7_6 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_6 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_6 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_6 : ∀ I J g, Xb2_3_7_6 I J g = Xcb2_3_7_6 I J g := by
  decide +kernel

theorem hYtabb2_3_7_6 : ∀ I J g, Yb2_3_7_6 I J g = Ycb2_3_7_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintb2_3_7_6 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_6 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_6 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_6 TL2_3_7 YLb2_3_7_6 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Xb2_3_7_7 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `7`. -/
noncomputable def Yb2_3_7_7 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_3 (fuseRow (2 : ZMod 8) (3 : ZMod 8) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `7`, pre-tabulated. -/
def XLb2_3_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `7`, pre-tabulated. -/
def YLb2_3_7_7 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_3_7_7 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLb2_3_7_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_3_7_7 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLb2_3_7_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_3_7_7 : ∀ I J g, Xb2_3_7_7 I J g = Xcb2_3_7_7 I J g := by
  decide +kernel

theorem hYtabb2_3_7_7 : ∀ I J g, Yb2_3_7_7 I J g = Ycb2_3_7_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `7`** (Koszul sign `-1`). -/
theorem hintb2_3_7_7 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xb2_3_7_7 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcb2_3_7_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_3_7_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yb2_3_7_7 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_2_3 hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycb2_3_7_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_3_7_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_3_7_7 TL2_3_7 YLb2_3_7_7 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_3_7_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_7_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_7_0 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_7_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_7_0 : ∀ I J g, Xc2_3_7_0 I J g = Xcc2_3_7_0 I J g := by
  decide +kernel

theorem hYtabc2_3_7_0 : ∀ I J g, Yc2_3_7_0 I J g = Ycc2_3_7_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_3_7_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xc2_3_7_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcc2_3_7_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_7_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yc2_3_7_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycc2_3_7_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_7_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_7_0 TL2_3_7 YLc2_3_7_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_3_7 (fuseRow (3 : ZMod 8) (7 : ZMod 8) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ro (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) ee) (fuseCol (3 : ZMod 8) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
      * fuseZ_2_2 (fuseRow (2 : ZMod 8) ((3 : ZMod 8) + 7) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 I) (ri (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 J) g) (fuseCol (2 : ZMod 8) ((3 : ZMod 8) + 7) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) = (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (3 : ZMod 8)).1 (realSize (2 : ZMod 8) (3 : ZMod 8)).2 (lo (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I)
          * realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_5_7 (fuseRow ((2 : ZMod 8) + 3) (7 : ZMod 8) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) I) (li (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 3) (7 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc2_3_7_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, -1], [0, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcc2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet XLc2_3_7_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_3_7_1 : (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2) → Fin (realRepDim ((2 : ZMod 8) + 3 + 7).val) → ℤ :=
  fun r s g => coeffGet YLc2_3_7_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 4 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_3_7_1 : ∀ I J g, Xc2_3_7_1 I J g = Xcc2_3_7_1 I J g := by
  decide +kernel

theorem hYtabc2_3_7_1 : ∀ I J g, Yc2_3_7_1 I J g = Ycc2_3_7_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc2_3_7_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))) * T2_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xc2_3_7_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hfuseZ_3_7 hfuseZ_2_2 (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Xcc2_3_7_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_3_7_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Yc2_3_7_1 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hfuseZ_5_7 (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 3 + 7)) Ycc2_3_7_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 3 7).1 ⊕ Fin (realGauge.gaugeSizeL 2 3 7).2)) (realRepBasis ((2 : ZMod 8) + 3 + 7)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_3_7_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 3 + 7) (realGauge.gaugeSizeL 2 3 7).1 (realGauge.gaugeSizeL 2 3 7).2 ((sgn (realRepBasisParity (7 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_3_7_1 TL2_3_7 YLc2_3_7_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_3_7 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_3_7
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_3_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_3_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_3_7_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_3_7 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T2_3_7
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_3_7_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_3_7_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_3_7_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintb2_3_7_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintb2_3_7_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintb2_3_7_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintb2_3_7_7

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_3_7 (i : Fin (realRepDim (7 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i)) * T2_3_7
      = ((sgn (realRepBasisParity (7 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_3_7 * (realGauge.gaugeRouteL (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) (realRepBasis (7 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h0]; exact hintc2_3_7_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) from Fin.ext h1]; exact hintc2_3_7_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_3_7_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 T2_3_7 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 hT2_3_7 hAint2_3_7 hBint2_3_7 hCint2_3_7

theorem gtOfT2_3_7_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 T2_3_7 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) hsz2_3_7 T2_3_7_ne_zero

theorem gInterSpace2_3_7_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_3_7_mem_gInterSpace, gtOfT2_3_7_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_3_7 : gParity ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (3 : ZMod 8) (7 : ZMod 8) gInterSpace2_3_7_ne_bot).symm

end Triple_2_3_7

/-! ### The triple `(2,4,0)`

`gaugeSizeL = gaugeSizeR = (1,1)`, `dim D_6 = 4`, certgen parity `0`; the unit-slot shortcut: the connector is the identity, so every certificate carries the sign `+1`. -/
section Triple_2_4_0
open Module
theorem hsz2_4_0 : realGauge.gaugeSizeR 2 4 0 = realGauge.gaugeSizeL 2 4 0 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`2 x 2 x 4`). -/
def TL2_4_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- The same literal read at the composite frame `Fin 1 ⊕ Fin 1`. -/
noncomputable def Tc2_4_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet TL2_4_0 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_6`. -/
noncomputable def T2_4_0 : ((realGauge.D ((2 : ZMod 8) + 4 + 0)).matrixSuper
    (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Tc2_4_0

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_4_0 : T2_4_0 ∈ ((realGauge.D ((2 : ZMod 8) + 4 + 0)).matrixSuper
    (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 4 + 0) Tc2_4_0 0 (by decide)

theorem T2_4_0_ne_zero : T2_4_0 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 4 + 0) Tc2_4_0 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xca2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_0_0 : ∀ I J g, Xa2_4_0_0 I J g = Xca2_4_0_0 I J g := by
  decide +kernel

theorem hYtaba2_4_0_0 : ∀ I J g, Ya2_4_0_0 I J g = Yca2_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_4_0_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xa2_4_0_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_2_4 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xca2_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ya2_4_0_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yca2_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_0_0 TL2_4_0 YLa2_4_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 1], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 1]],
   [[0, 0, 0, 1], [0, 0, 0, 0]]]

noncomputable def Xca2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_0_1 : ∀ I J g, Xa2_4_0_1 I J g = Xca2_4_0_1 I J g := by
  decide +kernel

theorem hYtaba2_4_0_1 : ∀ I J g, Ya2_4_0_1 I J g = Yca2_4_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta2_4_0_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xa2_4_0_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_2_4 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xca2_4_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ya2_4_0_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yca2_4_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_0_1 TL2_4_0 YLa2_4_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [1, 0, 0, 0]],
   [[-1, 0, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xca2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_0_2 : ∀ I J g, Xa2_4_0_2 I J g = Xca2_4_0_2 I J g := by
  decide +kernel

theorem hYtaba2_4_0_2 : ∀ I J g, Ya2_4_0_2 I J g = Yca2_4_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta2_4_0_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xa2_4_0_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_2_4 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xca2_4_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ya2_4_0_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yca2_4_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_0_2 TL2_4_0 YLa2_4_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (0 : ZMod 8)).1 (realSize (4 : ZMod 8) (0 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, -1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xca2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_0_3 : ∀ I J g, Xa2_4_0_3 I J g = Xca2_4_0_3 I J g := by
  decide +kernel

theorem hYtaba2_4_0_3 : ∀ I J g, Ya2_4_0_3 I J g = Yca2_4_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_4_0_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xa2_4_0_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_2_4 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xca2_4_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ya2_4_0_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yca2_4_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_0_3 TL2_4_0 YLa2_4_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcb2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_0_0 : ∀ I J g, Xb2_4_0_0 I J g = Xcb2_4_0_0 I J g := by
  decide +kernel

theorem hYtabb2_4_0_0 : ∀ I J g, Yb2_4_0_0 I J g = Ycb2_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_4_0_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xb2_4_0_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_4_0 hfuseZ_2_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xcb2_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yb2_4_0_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ycb2_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_0_0 TL2_4_0 YLb2_4_0_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_4_0_1 : List (List (List ℤ)) :=
  [[[0, 0, 0, 1], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 1]]]

noncomputable def Xcb2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_0_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_0_1 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_0_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_0_1 : ∀ I J g, Xb2_4_0_1 I J g = Xcb2_4_0_1 I J g := by
  decide +kernel

theorem hYtabb2_4_0_1 : ∀ I J g, Yb2_4_0_1 I J g = Ycb2_4_0_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb2_4_0_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xb2_4_0_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_4_0 hfuseZ_2_4 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xcb2_4_0_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_0_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yb2_4_0_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ycb2_4_0_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_0_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_0_1 TL2_4_0 YLb2_4_0_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_4_0_2 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 1, 0]],
   [[0, 0, -1, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_0_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_0_2 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_0_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_0_2 : ∀ I J g, Xb2_4_0_2 I J g = Xcb2_4_0_2 I J g := by
  decide +kernel

theorem hYtabb2_4_0_2 : ∀ I J g, Yb2_4_0_2 I J g = Ycb2_4_0_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb2_4_0_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xb2_4_0_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_4_0 hfuseZ_2_4 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xcb2_4_0_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_0_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yb2_4_0_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ycb2_4_0_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_0_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_0_2 TL2_4_0 YLb2_4_0_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_4_0_3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 1, 0, 0]],
   [[0, -1, 0, 0], [0, 0, 0, 0]]]

noncomputable def Xcb2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_0_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_0_3 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_0_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_0_3 : ∀ I J g, Xb2_4_0_3 I J g = Xcb2_4_0_3 I J g := by
  decide +kernel

theorem hYtabb2_4_0_3 : ∀ I J g, Yb2_4_0_3 I J g = Ycb2_4_0_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_4_0_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xb2_4_0_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_4_0 hfuseZ_2_4 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xcb2_4_0_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_0_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yb2_4_0_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_2_4 hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ycb2_4_0_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_0_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_0_3 TL2_4_0 YLb2_4_0_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_0 (fuseRow (4 : ZMod 8) (0 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ro (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) ee) (fuseCol (4 : ZMod 8) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
      * fuseZ_2_4 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 0) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 I) (ri (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 0) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I)
          * realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_0 (fuseRow ((2 : ZMod 8) + 4) (0 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_4_0_0 : List (List (List ℤ)) :=
  [[[1, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [1, 0, 0, 0]]]

noncomputable def Xcc2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_0_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_0_0 : (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 0).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_0_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `2² · 4 = 16` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_0_0 : ∀ I J g, Xc2_4_0_0 I J g = Xcc2_4_0_0 I J g := by
  decide +kernel

theorem hYtabc2_4_0_0 : ∀ I J g, Yc2_4_0_0 I J g = Ycc2_4_0_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_4_0_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)))) * T2_4_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xc2_4_0_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hfuseZ_4_0 hfuseZ_2_4 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Xcc2_4_0_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_0_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Yc2_4_0_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hfuseZ_6_0 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 0)) Ycc2_4_0_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 0).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 0).2)) (realRepBasis ((2 : ZMod 8) + 4 + 0)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_0_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 0) (realGauge.gaugeSizeL 2 4 0).1 (realGauge.gaugeSizeL 2 4 0).2 ((sgn (realRepBasisParity (0 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_0_0 TL2_4_0 YLc2_4_0_0 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_4_0 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_4_0
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_4_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_4_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_4_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_4_0_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_4_0 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T2_4_0
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_4_0_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_4_0_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_4_0_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_4_0_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_4_0 (i : Fin (realRepDim (0 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i)) * T2_4_0
      = ((sgn (realRepBasisParity (0 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_0 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) (realRepBasis (0 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 1 := i.isLt
  have h0 : (i : ℕ) = 0 := by omega
  rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (0 : ZMod 8).val)) from Fin.ext h0]
  exact hintc2_4_0_0

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_4_0_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 T2_4_0 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 hT2_4_0 hAint2_4_0 hBint2_4_0 hCint2_4_0

theorem gtOfT2_4_0_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 T2_4_0 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) hsz2_4_0 T2_4_0_ne_zero

theorem gInterSpace2_4_0_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_4_0_mem_gInterSpace, gtOfT2_4_0_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_4_0 : gParity ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (0 : ZMod 8) gInterSpace2_4_0_ne_bot).symm

end Triple_2_4_0

/-! ### The triple `(2,4,1)`

`gaugeSizeL = gaugeSizeR = (2,2)`, `dim D_7 = 2`, certgen parity `1`; the transported connector literal. -/
section Triple_2_4_1
open Module
theorem hsz2_4_1 : realGauge.gaugeSizeR 2 4 1 = realGauge.gaugeSizeL 2 4 1 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`4 x 4 x 2`). -/
def TL2_4_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, -1], [1, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [-1, 0], [0, -1], [0, 0]]]

/-- The same literal read at the composite frame `Fin 2 ⊕ Fin 2`. -/
noncomputable def Tc2_4_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet TL2_4_1 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_7`. -/
noncomputable def T2_4_1 : ((realGauge.D ((2 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Tc2_4_1

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_4_1 : T2_4_1 ∈ ((realGauge.D ((2 : ZMod 8) + 4 + 1)).matrixSuper
    (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2).grading 1 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 4 + 1) Tc2_4_1 1 (by decide)

theorem T2_4_1_ne_zero : T2_4_1 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 4 + 1) Tc2_4_1 (Sum.inl ⟨0, by decide⟩) (Sum.inr ⟨0, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_1_0 : ∀ I J g, Xa2_4_1_0 I J g = Xca2_4_1_0 I J g := by
  decide +kernel

theorem hYtaba2_4_1_0 : ∀ I J g, Ya2_4_1_0 I J g = Yca2_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_4_1_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xa2_4_1_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xca2_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ya2_4_1_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yca2_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_4_1_0 TL2_4_1 YLa2_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xca2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_1_1 : ∀ I J g, Xa2_4_1_1 I J g = Xca2_4_1_1 I J g := by
  decide +kernel

theorem hYtaba2_4_1_1 : ∀ I J g, Ya2_4_1_1 I J g = Yca2_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `-1`). -/
theorem hinta2_4_1_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xa2_4_1_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_2_5 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xca2_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ya2_4_1_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yca2_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_4_1_1 TL2_4_1 YLa2_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_1_2 : ∀ I J g, Xa2_4_1_2 I J g = Xca2_4_1_2 I J g := by
  decide +kernel

theorem hYtaba2_4_1_2 : ∀ I J g, Ya2_4_1_2 I J g = Yca2_4_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `-1`). -/
theorem hinta2_4_1_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xa2_4_1_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_2_5 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xca2_4_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ya2_4_1_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yca2_4_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_4_1_2 TL2_4_1 YLa2_4_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (1 : ZMod 8)).1 (realSize (4 : ZMod 8) (1 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xca2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_1_3 : ∀ I J g, Xa2_4_1_3 I J g = Xca2_4_1_3 I J g := by
  decide +kernel

theorem hYtaba2_4_1_3 : ∀ I J g, Ya2_4_1_3 I J g = Yca2_4_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_4_1_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xa2_4_1_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_2_5 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (5 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xca2_4_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ya2_4_1_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yca2_4_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLa2_4_1_3 TL2_4_1 YLa2_4_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_1_0 : ∀ I J g, Xb2_4_1_0 I J g = Xcb2_4_1_0 I J g := by
  decide +kernel

theorem hYtabb2_4_1_0 : ∀ I J g, Yb2_4_1_0 I J g = Ycb2_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_4_1_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xb2_4_1_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcb2_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yb2_4_1_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycb2_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_4_1_0 TL2_4_1 YLb2_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0]]]

noncomputable def Xcb2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_1_1 : ∀ I J g, Xb2_4_1_1 I J g = Xcb2_4_1_1 I J g := by
  decide +kernel

theorem hYtabb2_4_1_1 : ∀ I J g, Yb2_4_1_1 I J g = Ycb2_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb2_4_1_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xb2_4_1_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcb2_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yb2_4_1_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycb2_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_4_1_1 TL2_4_1 YLb2_4_1_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_4_1_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_1_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_1_2 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_1_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_1_2 : ∀ I J g, Xb2_4_1_2 I J g = Xcb2_4_1_2 I J g := by
  decide +kernel

theorem hYtabb2_4_1_2 : ∀ I J g, Yb2_4_1_2 I J g = Ycb2_4_1_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb2_4_1_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xb2_4_1_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcb2_4_1_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_1_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yb2_4_1_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycb2_4_1_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_1_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_4_1_2 TL2_4_1 YLb2_4_1_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_4_1_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_1_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_1_3 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_1_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_1_3 : ∀ I J g, Xb2_4_1_3 I J g = Xcb2_4_1_3 I J g := by
  decide +kernel

theorem hYtabb2_4_1_3 : ∀ I J g, Yb2_4_1_3 I J g = Ycb2_4_1_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_4_1_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xb2_4_1_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcb2_4_1_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_1_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yb2_4_1_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_2_4 hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycb2_4_1_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_1_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLb2_4_1_3 TL2_4_1 YLb2_4_1_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_4_1_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_1_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_1_0 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_1_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_1_0 : ∀ I J g, Xc2_4_1_0 I J g = Xcc2_4_1_0 I J g := by
  decide +kernel

theorem hYtabc2_4_1_0 : ∀ I J g, Yc2_4_1_0 I J g = Ycc2_4_1_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_4_1_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xc2_4_1_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcc2_4_1_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_1_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yc2_4_1_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycc2_4_1_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_1_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_4_1_0 TL2_4_1 YLc2_4_1_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_1 (fuseRow (4 : ZMod 8) (1 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ro (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) ee) (fuseCol (4 : ZMod 8) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
      * fuseZ_2_5 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 1) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 I) (ri (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 1) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I)
          * realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_1 (fuseRow ((2 : ZMod 8) + 4) (1 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (1 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 1], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc2_4_1_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0]]]

noncomputable def Xcc2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_1_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_1_1 : (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 1).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_1_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `4² · 2 = 32` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_1_1 : ∀ I J g, Xc2_4_1_1 I J g = Xcc2_4_1_1 I J g := by
  decide +kernel

theorem hYtabc2_4_1_1 : ∀ I J g, Yc2_4_1_1 I J g = Ycc2_4_1_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `-1`). -/
theorem hintc2_4_1_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)))) * T2_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ) • (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xc2_4_1_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hfuseZ_4_1 hfuseZ_2_5 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Xcc2_4_1_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_1_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Yc2_4_1_1 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hfuseZ_6_1 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 1)) Ycc2_4_1_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 1).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 1).2)) (realRepBasis ((2 : ZMod 8) + 4 + 1)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_1_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 1) (realGauge.gaugeSizeL 2 4 1).1 (realGauge.gaugeSizeL 2 4 1).2 ((sgn (realRepBasisParity (1 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) * 1) : ℤˣ) : ℤ)
    XLc2_4_1_1 TL2_4_1 YLc2_4_1_1 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_4_1 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_4_1
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_4_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_4_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_4_1_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_4_1 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T2_4_1
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_4_1_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_4_1_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_4_1_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_4_1 (i : Fin (realRepDim (1 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i)) * T2_4_1
      = ((sgn (realRepBasisParity (1 : ZMod 8) i * 1) : ℤˣ) : ℤ) •
          (T2_4_1 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) (realRepBasis (1 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 2 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h0]; exact hintc2_4_1_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (1 : ZMod 8).val)) from Fin.ext h1]; exact hintc2_4_1_1

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_4_1_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 T2_4_1 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 hT2_4_1 hAint2_4_1 hBint2_4_1 hCint2_4_1

theorem gtOfT2_4_1_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 T2_4_1 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) hsz2_4_1 T2_4_1_ne_zero

theorem gInterSpace2_4_1_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) 1 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_4_1_mem_gInterSpace, gtOfT2_4_1_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_4_1 : gParity ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) = 1 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (1 : ZMod 8) gInterSpace2_4_1_ne_bot).symm

end Triple_2_4_1

/-! ### The triple `(2,4,2)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_0 = 1`, certgen parity `0`; the transported connector literal. -/
section Triple_2_4_2
open Module
theorem hsz2_4_2 : realGauge.gaugeSizeR 2 4 2 = realGauge.gaugeSizeL 2 4 2 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 1`). -/
def TL2_4_2 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc2_4_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet TL2_4_2 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_0`. -/
noncomputable def T2_4_2 : ((realGauge.D ((2 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Tc2_4_2

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_4_2 : T2_4_2 ∈ ((realGauge.D ((2 : ZMod 8) + 4 + 2)).matrixSuper
    (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 4 + 2) Tc2_4_2 0 (by decide)

theorem T2_4_2_ne_zero : T2_4_2 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 4 + 2) Tc2_4_2 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨2, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xca2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_2_0 : ∀ I J g, Xa2_4_2_0 I J g = Xca2_4_2_0 I J g := by
  decide +kernel

theorem hYtaba2_4_2_0 : ∀ I J g, Ya2_4_2_0 I J g = Yca2_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_4_2_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xa2_4_2_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xca2_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ya2_4_2_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yca2_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_2_0 TL2_4_2 YLa2_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_2_1 : ∀ I J g, Xa2_4_2_1 I J g = Xca2_4_2_1 I J g := by
  decide +kernel

theorem hYtaba2_4_2_1 : ∀ I J g, Ya2_4_2_1 I J g = Yca2_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta2_4_2_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xa2_4_2_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_2_6 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xca2_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ya2_4_2_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yca2_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_2_1 TL2_4_2 YLa2_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

noncomputable def Xca2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_2_2 : ∀ I J g, Xa2_4_2_2 I J g = Xca2_4_2_2 I J g := by
  decide +kernel

theorem hYtaba2_4_2_2 : ∀ I J g, Ya2_4_2_2 I J g = Yca2_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta2_4_2_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xa2_4_2_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_2_6 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xca2_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ya2_4_2_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yca2_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_2_2 TL2_4_2 YLa2_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (2 : ZMod 8)).1 (realSize (4 : ZMod 8) (2 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xca2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_2_3 : ∀ I J g, Xa2_4_2_3 I J g = Xca2_4_2_3 I J g := by
  decide +kernel

theorem hYtaba2_4_2_3 : ∀ I J g, Ya2_4_2_3 I J g = Yca2_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_4_2_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xa2_4_2_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_2_6 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xca2_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ya2_4_2_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yca2_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_2_3 TL2_4_2 YLa2_4_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcb2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_2_0 : ∀ I J g, Xb2_4_2_0 I J g = Xcb2_4_2_0 I J g := by
  decide +kernel

theorem hYtabb2_4_2_0 : ∀ I J g, Yb2_4_2_0 I J g = Ycb2_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_4_2_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xb2_4_2_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcb2_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yb2_4_2_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycb2_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_2_0 TL2_4_2 YLb2_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcb2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_2_1 : ∀ I J g, Xb2_4_2_1 I J g = Xcb2_4_2_1 I J g := by
  decide +kernel

theorem hYtabb2_4_2_1 : ∀ I J g, Yb2_4_2_1 I J g = Ycb2_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb2_4_2_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xb2_4_2_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcb2_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yb2_4_2_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycb2_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_2_1 TL2_4_2 YLb2_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]]]

noncomputable def Xcb2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_2_2 : ∀ I J g, Xb2_4_2_2 I J g = Xcb2_4_2_2 I J g := by
  decide +kernel

theorem hYtabb2_4_2_2 : ∀ I J g, Yb2_4_2_2 I J g = Ycb2_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb2_4_2_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xb2_4_2_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcb2_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yb2_4_2_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycb2_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_2_2 TL2_4_2 YLb2_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]]]

noncomputable def Xcb2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_2_3 : ∀ I J g, Xb2_4_2_3 I J g = Xcb2_4_2_3 I J g := by
  decide +kernel

theorem hYtabb2_4_2_3 : ∀ I J g, Yb2_4_2_3 I J g = Ycb2_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_4_2_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xb2_4_2_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcb2_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yb2_4_2_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_2_4 hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycb2_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_2_3 TL2_4_2 YLb2_4_2_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_4_2_0 : List (List (List ℤ)) :=
  [[[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]]]

noncomputable def Xcc2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_2_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_2_0 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_2_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_2_0 : ∀ I J g, Xc2_4_2_0 I J g = Xcc2_4_2_0 I J g := by
  decide +kernel

theorem hYtabc2_4_2_0 : ∀ I J g, Yc2_4_2_0 I J g = Ycc2_4_2_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_4_2_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xc2_4_2_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcc2_4_2_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_2_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yc2_4_2_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycc2_4_2_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_2_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_2_0 TL2_4_2 YLc2_4_2_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc2_4_2_1 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]]]

noncomputable def Xcc2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_2_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_2_1 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_2_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_2_1 : ∀ I J g, Xc2_4_2_1 I J g = Xcc2_4_2_1 I J g := by
  decide +kernel

theorem hYtabc2_4_2_1 : ∀ I J g, Yc2_4_2_1 I J g = Ycc2_4_2_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc2_4_2_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xc2_4_2_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcc2_4_2_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_2_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yc2_4_2_1 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycc2_4_2_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_2_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_2_1 TL2_4_2 YLc2_4_2_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [-1], [0], [0], [0], [0], [0], [0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc2_4_2_2 : List (List (List ℤ)) :=
  [[[0], [0], [0], [0], [0], [1], [0], [0]],
   [[0], [0], [0], [0], [-1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [-1]],
   [[0], [0], [0], [0], [0], [0], [1], [0]],
   [[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]]]

noncomputable def Xcc2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_2_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_2_2 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_2_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_2_2 : ∀ I J g, Xc2_4_2_2 I J g = Xcc2_4_2_2 I J g := by
  decide +kernel

theorem hYtabc2_4_2_2 : ∀ I J g, Yc2_4_2_2 I J g = Ycc2_4_2_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc2_4_2_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xc2_4_2_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcc2_4_2_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_2_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yc2_4_2_2 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycc2_4_2_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_2_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_2_2 TL2_4_2 YLc2_4_2_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_2 (fuseRow (4 : ZMod 8) (2 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ro (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) ee) (fuseCol (4 : ZMod 8) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
      * fuseZ_2_6 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 2) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 I) (ri (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 2) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_2 (fuseRow ((2 : ZMod 8) + 4) (2 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [-1], [0], [0], [0], [0], [0], [0]],
   [[1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [1], [0], [0], [0], [0]],
   [[0], [0], [-1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc2_4_2_3 : List (List (List ℤ)) :=
  [[[0], [1], [0], [0], [0], [0], [0], [0]],
   [[-1], [0], [0], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [-1], [0], [0], [0], [0]],
   [[0], [0], [1], [0], [0], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [-1], [0], [0]],
   [[0], [0], [0], [0], [1], [0], [0], [0]],
   [[0], [0], [0], [0], [0], [0], [0], [1]],
   [[0], [0], [0], [0], [0], [0], [-1], [0]]]

noncomputable def Xcc2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_2_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_2_3 : (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 2).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_2_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 1 = 64` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_2_3 : ∀ I J g, Xc2_4_2_3 I J g = Xcc2_4_2_3 I J g := by
  decide +kernel

theorem hYtabc2_4_2_3 : ∀ I J g, Yc2_4_2_3 I J g = Ycc2_4_2_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc2_4_2_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xc2_4_2_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hfuseZ_4_2 hfuseZ_2_6 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Xcc2_4_2_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_2_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Yc2_4_2_3 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hfuseZ_6_2 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 2)) Ycc2_4_2_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 2).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 2).2)) (realRepBasis ((2 : ZMod 8) + 4 + 2)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_2_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 2) (realGauge.gaugeSizeL 2 4 2).1 (realGauge.gaugeSizeL 2 4 2).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_2_3 TL2_4_2 YLc2_4_2_3 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_4_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_4_2_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_4_2 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T2_4_2
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_4_2_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_4_2 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_4_2
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_2 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hintc2_4_2_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hintc2_4_2_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hintc2_4_2_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hintc2_4_2_3

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_4_2_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 T2_4_2 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 hT2_4_2 hAint2_4_2 hBint2_4_2 hCint2_4_2

theorem gtOfT2_4_2_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 T2_4_2 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) hsz2_4_2 T2_4_2_ne_zero

theorem gInterSpace2_4_2_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_4_2_mem_gInterSpace, gtOfT2_4_2_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_4_2 : gParity ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (2 : ZMod 8) gInterSpace2_4_2_ne_bot).symm

end Triple_2_4_2

/-! ### The triple `(2,4,3)`

`gaugeSizeL = gaugeSizeR = (4,4)`, `dim D_1 = 2`, certgen parity `0`; the transported connector literal. -/
section Triple_2_4_3
open Module
theorem hsz2_4_3 : realGauge.gaugeSizeR 2 4 3 = realGauge.gaugeSizeL 2 4 3 := by decide

/-- **The frozen connector**, transported to the Lean frame order, as a
nested integer list literal (`8 x 8 x 2`). -/
def TL2_4_3 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [-1, 0], [0, -1], [0, 0], [0, 1], [0, 0]],
   [[1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, -1]],
   [[-1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 1]],
   [[0, 0], [-1, 0], [0, 0], [-1, 0], [0, -1], [0, 0], [0, -1], [0, 0]],
   [[0, -1], [0, 0], [0, -1], [0, 0], [0, 0], [1, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 1], [0, 0], [0, -1], [-1, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, -1], [-1, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 1], [0, 0], [0, -1], [0, 0], [0, 0], [1, 0], [0, 0], [-1, 0]]]

/-- The same literal read at the composite frame `Fin 4 ⊕ Fin 4`. -/
noncomputable def Tc2_4_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet TL2_4_3 (sumPos r) (sumPos s) g.val

/-- **The connector** as a matrix over `D_1`. -/
noncomputable def T2_4_3 : ((realGauge.D ((2 : ZMod 8) + 4 + 3)).matrixSuper
    (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2).carrier :=
  matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Tc2_4_3

/-- **Hypothesis 2 of `gtOfT_mem_interSpace`** — the connector is homogeneous. -/
theorem hT2_4_3 : T2_4_3 ∈ ((realGauge.D ((2 : ZMod 8) + 4 + 3)).matrixSuper
    (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2).grading 0 :=
  matOfCoeff_mem_matrixGrading ((2 : ZMod 8) + 4 + 3) Tc2_4_3 0 (by decide)

theorem T2_4_3_ne_zero : T2_4_3 ≠ 0 :=
  matOfCoeff_ne_zero ((2 : ZMod 8) + 4 + 3) Tc2_4_3 (Sum.inl ⟨0, by decide⟩) (Sum.inl ⟨1, by decide⟩) ⟨0, by decide⟩ (by decide)

/-- Right-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Xa2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I)
          * realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `0`. -/
noncomputable def Ya2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `0`, pre-tabulated. -/
def XLa2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `a`-slot generator `0`, pre-tabulated. -/
def YLa2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xca2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_3_0 : ∀ I J g, Xa2_4_3_0 I J g = Xca2_4_3_0 I J g := by
  decide +kernel

theorem hYtaba2_4_3_0 : ∀ I J g, Ya2_4_3_0 I J g = Yca2_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `0`** (Koszul sign `+1`). -/
theorem hinta2_4_3_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xa2_4_3_0 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xca2_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ya2_4_3_0 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yca2_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_3_0 TL2_4_3 YLa2_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Xa2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I)
          * realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `1`. -/
noncomputable def Ya2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `1`, pre-tabulated. -/
def XLa2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

/-- Left route at the `a`-slot generator `1`, pre-tabulated. -/
def YLa2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_3_1 : ∀ I J g, Xa2_4_3_1 I J g = Xca2_4_3_1 I J g := by
  decide +kernel

theorem hYtaba2_4_3_1 : ∀ I J g, Ya2_4_3_1 I J g = Yca2_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `1`** (Koszul sign `+1`). -/
theorem hinta2_4_3_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xa2_4_3_1 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_2_7 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xca2_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ya2_4_3_1 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yca2_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_3_1 TL2_4_3 YLa2_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Xa2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I)
          * realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `2`. -/
noncomputable def Ya2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `2`, pre-tabulated. -/
def XLa2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `2`, pre-tabulated. -/
def YLa2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xca2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_3_2 : ∀ I J g, Xa2_4_3_2 I J g = Xca2_4_3_2 I J g := by
  decide +kernel

theorem hYtaba2_4_3_2 : ∀ I J g, Ya2_4_3_2 I J g = Yca2_4_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `2`** (Koszul sign `+1`). -/
theorem hinta2_4_3_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xa2_4_3_2 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_2_7 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xca2_4_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ya2_4_3_2 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yca2_4_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_3_2 TL2_4_3 YLa2_4_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Xa2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) = (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) then
      ((sgn (sumParity (realSize (4 : ZMod 8) (3 : ZMod 8)).1 (realSize (4 : ZMod 8) (3 : ZMod 8)).2 (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I)
          * realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)))
    else 0

/-- Left-route coefficient array at the `a`-slot generator `3`. -/
noncomputable def Ya2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `a`-slot generator `3`, pre-tabulated. -/
def XLa2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `a`-slot generator `3`, pre-tabulated. -/
def YLa2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xca2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLa2_4_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Yca2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLa2_4_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtaba2_4_3_3 : ∀ I J g, Xa2_4_3_3 I J g = Xca2_4_3_3 I J g := by
  decide +kernel

theorem hYtaba2_4_3_3 : ∀ I J g, Ya2_4_3_3 I J g = Yca2_4_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `a`-slot generator `3`** (Koszul sign `+1`). -/
theorem hinta2_4_3_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xa2_4_3_3 := Matrix.ext fun I J => routeR'_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_2_7 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (7 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xca2_4_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtaba2_4_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ya2_4_3_3 := Matrix.ext fun I J => routeL_aSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yca2_4_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtaba2_4_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (2 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLa2_4_3_3 TL2_4_3 YLa2_4_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Xb2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `0`. -/
noncomputable def Yb2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `0`, pre-tabulated. -/
def XLb2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `b`-slot generator `0`, pre-tabulated. -/
def YLb2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcb2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_3_0 : ∀ I J g, Xb2_4_3_0 I J g = Xcb2_4_3_0 I J g := by
  decide +kernel

theorem hYtabb2_4_3_0 : ∀ I J g, Yb2_4_3_0 I J g = Ycb2_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintb2_4_3_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xb2_4_3_0 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcb2_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yb2_4_3_0 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycb2_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_3_0 TL2_4_3 YLb2_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Xb2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `1`. -/
noncomputable def Yb2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `1`, pre-tabulated. -/
def XLb2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `1`, pre-tabulated. -/
def YLb2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcb2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_3_1 : ∀ I J g, Xb2_4_3_1 I J g = Xcb2_4_3_1 I J g := by
  decide +kernel

theorem hYtabb2_4_3_1 : ∀ I J g, Yb2_4_3_1 I J g = Ycb2_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintb2_4_3_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xb2_4_3_1 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcb2_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yb2_4_3_1 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycb2_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_3_1 TL2_4_3 YLb2_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Xb2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `2`. -/
noncomputable def Yb2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `2`, pre-tabulated. -/
def XLb2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `2`, pre-tabulated. -/
def YLb2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcb2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_3_2 : ∀ I J g, Xb2_4_3_2 I J g = Xcb2_4_3_2 I J g := by
  decide +kernel

theorem hYtabb2_4_3_2 : ∀ I J g, Yb2_4_3_2 I J g = Ycb2_4_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintb2_4_3_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xb2_4_3_2 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcb2_4_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yb2_4_3_2 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycb2_4_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_3_2 TL2_4_3 YLb2_4_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Xb2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `b`-slot generator `3`. -/
noncomputable def Yb2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_2_4 (fuseRow (2 : ZMod 8) (4 : ZMod 8) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) ee) (fuseCol (2 : ZMod 8) (4 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))
      * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) ee (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))

/-- Right route at the `b`-slot generator `3`, pre-tabulated. -/
def XLb2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `b`-slot generator `3`, pre-tabulated. -/
def YLb2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

noncomputable def Xcb2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLb2_4_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycb2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLb2_4_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabb2_4_3_3 : ∀ I J g, Xb2_4_3_3 I J g = Xcb2_4_3_3 I J g := by
  decide +kernel

theorem hYtabb2_4_3_3 : ∀ I J g, Yb2_4_3_3 I J g = Ycb2_4_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `b`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintb2_4_3_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xb2_4_3_3 := Matrix.ext fun I J => routeR'_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcb2_4_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabb2_4_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yb2_4_3_3 := Matrix.ext fun I J => routeL_bSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_2_4 hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) rfl I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycb2_4_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabb2_4_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (4 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLb2_4_3_3 TL2_4_3 YLb2_4_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Xc2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `0`. -/
noncomputable def Yc2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `0`, pre-tabulated. -/
def XLc2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

/-- Left route at the `c`-slot generator `0`, pre-tabulated. -/
def YLc2_4_3_0 : List (List (List ℤ)) :=
  [[[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]]]

noncomputable def Xcc2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_0 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_0 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_0 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_0 : ∀ I J g, Xc2_4_3_0 I J g = Xcc2_4_3_0 I J g := by
  decide +kernel

theorem hYtabc2_4_3_0 : ∀ I J g, Yc2_4_3_0 I J g = Ycc2_4_3_0 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `0`** (Koszul sign `+1`). -/
theorem hintc2_4_3_0 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_0 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_0 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_0 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_0 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_0 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_0 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_0 TL2_4_3 YLc2_4_3_0 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Xc2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `1`. -/
noncomputable def Yc2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `1`, pre-tabulated. -/
def XLc2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `1`, pre-tabulated. -/
def YLc2_4_3_1 : List (List (List ℤ)) :=
  [[[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]]]

noncomputable def Xcc2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_1 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_1 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_1 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_1 : ∀ I J g, Xc2_4_3_1 I J g = Xcc2_4_3_1 I J g := by
  decide +kernel

theorem hYtabc2_4_3_1 : ∀ I J g, Yc2_4_3_1 I J g = Ycc2_4_3_1 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `1`** (Koszul sign `+1`). -/
theorem hintc2_4_3_1 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_1 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_1 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_1 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_1 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_1 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_1 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_1 TL2_4_3 YLc2_4_3_1 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Xc2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `2`. -/
noncomputable def Yc2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `2`, pre-tabulated. -/
def XLc2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `2`, pre-tabulated. -/
def YLc2_4_3_2 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_2 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_2 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_2 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_2 : ∀ I J g, Xc2_4_3_2 I J g = Xcc2_4_3_2 I J g := by
  decide +kernel

theorem hYtabc2_4_3_2 : ∀ I J g, Yc2_4_3_2 I J g = Ycc2_4_3_2 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `2`** (Koszul sign `+1`). -/
theorem hintc2_4_3_2 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_2 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_2 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_2 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_2 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_2 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_2 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_2 TL2_4_3 YLc2_4_3_2 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Xc2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `3`. -/
noncomputable def Yc2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `3`, pre-tabulated. -/
def XLc2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `3`, pre-tabulated. -/
def YLc2_4_3_3 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_3 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_3 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_3 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_3 : ∀ I J g, Xc2_4_3_3 I J g = Xcc2_4_3_3 I J g := by
  decide +kernel

theorem hYtabc2_4_3_3 : ∀ I J g, Yc2_4_3_3 I J g = Ycc2_4_3_3 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `3`** (Koszul sign `+1`). -/
theorem hintc2_4_3_3 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_3 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_3 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_3 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_3 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_3 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_3 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_3 TL2_4_3 YLc2_4_3_3 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Xc2_4_3_4 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `4`. -/
noncomputable def Yc2_4_3_4 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `4`, pre-tabulated. -/
def XLc2_4_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `4`, pre-tabulated. -/
def YLc2_4_3_4 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc2_4_3_4 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_4 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_4 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_4 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_4 : ∀ I J g, Xc2_4_3_4 I J g = Xcc2_4_3_4 I J g := by
  decide +kernel

theorem hYtabc2_4_3_4 : ∀ I J g, Yc2_4_3_4 I J g = Ycc2_4_3_4 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `4`** (Koszul sign `+1`). -/
theorem hintc2_4_3_4 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_4 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_4 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_4 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_4 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_4 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_4 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_4 TL2_4_3 YLc2_4_3_4 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Xc2_4_3_5 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `5`. -/
noncomputable def Yc2_4_3_5 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `5`, pre-tabulated. -/
def XLc2_4_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `5`, pre-tabulated. -/
def YLc2_4_3_5 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]],
   [[0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

noncomputable def Xcc2_4_3_5 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_5 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_5 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_5 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_5 : ∀ I J g, Xc2_4_3_5 I J g = Xcc2_4_3_5 I J g := by
  decide +kernel

theorem hYtabc2_4_3_5 : ∀ I J g, Yc2_4_3_5 I J g = Ycc2_4_3_5 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `5`** (Koszul sign `+1`). -/
theorem hintc2_4_3_5 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_5 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_5 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_5 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_5 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_5 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_5 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_5 TL2_4_3 YLc2_4_3_5 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Xc2_4_3_6 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `6`. -/
noncomputable def Yc2_4_3_6 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `6`, pre-tabulated. -/
def XLc2_4_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `6`, pre-tabulated. -/
def YLc2_4_3_6 : List (List (List ℤ)) :=
  [[[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[-1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [-1, 0], [0, 0]]]

noncomputable def Xcc2_4_3_6 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_6 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_6 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_6 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_6 : ∀ I J g, Xc2_4_3_6 I J g = Xcc2_4_3_6 I J g := by
  decide +kernel

theorem hYtabc2_4_3_6 : ∀ I J g, Yc2_4_3_6 I J g = Ycc2_4_3_6 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `6`** (Koszul sign `+1`). -/
theorem hintc2_4_3_6 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_6 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_6 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_6 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_6 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_6 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_6 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_6 TL2_4_3 YLc2_4_3_6 (by decide +kernel)

/-- Right-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Xc2_4_3_7 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => ∑ ee, fuseZ_4_3 (fuseRow (4 : ZMod 8) (3 : ZMod 8) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ro (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) ee) (fuseCol (4 : ZMod 8) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
      * fuseZ_2_7 (fuseRow (2 : ZMod 8) ((4 : ZMod 8) + 3) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 I) (ri (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 J) g) (fuseCol (2 : ZMod 8) ((4 : ZMod 8) + 3) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) ee)

/-- Left-route coefficient array at the `c`-slot generator `7`. -/
noncomputable def Yc2_4_3_7 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun I J g => if (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) = (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) then
      ((sgn (sumParity (realSize (2 : ZMod 8) (4 : ZMod 8)).1 (realSize (2 : ZMod 8) (4 : ZMod 8)).2 (lo (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I)
          * realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))) : ℤˣ) : ℤ)
        * fuseZ_6_3 (fuseRow ((2 : ZMod 8) + 4) (3 : ZMod 8) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) I) (li (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) J) g) (fuseCol ((2 : ZMod 8) + 4) (3 : ZMod 8) (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))
    else 0

/-- Right route at the `c`-slot generator `7`, pre-tabulated. -/
def XLc2_4_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [0, 0], [0, 0]]]

/-- Left route at the `c`-slot generator `7`, pre-tabulated. -/
def YLc2_4_3_7 : List (List (List ℤ)) :=
  [[[0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, -1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, -1], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -1]],
   [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [0, 0]]]

noncomputable def Xcc2_4_3_7 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet XLc2_4_3_7 (sumPos r) (sumPos s) g.val

noncomputable def Ycc2_4_3_7 : (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2) → Fin (realRepDim ((2 : ZMod 8) + 4 + 3).val) → ℤ :=
  fun r s g => coeffGet YLc2_4_3_7 (sumPos r) (sumPos s) g.val

/-- **The tabulation**: the route formula agrees with the literal at
all `8² · 2 = 128` entries.  This is the ONLY check that evaluates the
route's own frame equivalences (`ro`/`ri`, `lo`/`li`) — once per ENTRY.
The convolution below sees list literals and nothing else. -/
theorem hXtabc2_4_3_7 : ∀ I J g, Xc2_4_3_7 I J g = Xcc2_4_3_7 I J g := by
  decide +kernel

theorem hYtabc2_4_3_7 : ∀ I J g, Yc2_4_3_7 I J g = Ycc2_4_3_7 I J g := by
  decide +kernel

/-- **The intertwining certificate at the `c`-slot generator `7`** (Koszul sign `+1`). -/
theorem hintc2_4_3_7 :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)))) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ) • (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))) := by
  have hX0 : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xc2_4_3_7 := Matrix.ext fun I J => routeR'_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hfuseZ_4_3 hfuseZ_2_7 (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) rfl I J
  have hX : (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Xcc2_4_3_7 :=
    hX0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hXtabc2_4_3_7 I J g))
  have hY0 : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Yc2_4_3_7 := Matrix.ext fun I J => routeL_cSlot_coeff (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hfuseZ_6_3 (⟨0, by decide⟩ : Fin (realRepDim (6 : ZMod 8).val)) rfl (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) I J
  have hY : (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val))))
      = matOfCoeff (realRepBasis ((2 : ZMod 8) + 4 + 3)) Ycc2_4_3_7 :=
    hY0.trans (congrArg (matOfCoeff (ι := (Fin (realGauge.gaugeSizeL 2 4 3).1 ⊕ Fin (realGauge.gaugeSizeL 2 4 3).2)) (realRepBasis ((2 : ZMod 8) + 4 + 3)))
      (funext fun I => funext fun J => funext fun g => hYtabc2_4_3_7 I J g))
  rw [hX, hY]
  exact realCheckMatEq_sumPos ((2 : ZMod 8) + 4 + 3) (realGauge.gaugeSizeL 2 4 3).1 (realGauge.gaugeSizeL 2 4 3).2 ((sgn (realRepBasisParity (3 : ZMod 8) (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) * 0) : ℤˣ) : ℤ)
    XLc2_4_3_7 TL2_4_3 YLc2_4_3_7 (by decide +kernel)

/-- **Hypothesis 3, `a`-slot family.** -/
theorem hAint2_4_3 (i : Fin (realRepDim (2 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i)) * T2_4_3
      = ((sgn (realRepBasisParity (2 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (aSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (2 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h0]; exact hinta2_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h1]; exact hinta2_4_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h2]; exact hinta2_4_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (2 : ZMod 8).val)) from Fin.ext h3]; exact hinta2_4_3_3

/-- **Hypothesis 3, `b`-slot family.** -/
theorem hBint2_4_3 (i : Fin (realRepDim (4 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) i)) * T2_4_3
      = ((sgn (realRepBasisParity (4 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (bSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (4 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 4 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h0 | h1 | h2 | h3
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h0]; exact hintb2_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h1]; exact hintb2_4_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h2]; exact hintb2_4_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (4 : ZMod 8).val)) from Fin.ext h3]; exact hintb2_4_3_3

/-- **Hypothesis 3, `c`-slot family.** -/
theorem hCint2_4_3 (i : Fin (realRepDim (3 : ZMod 8).val)) :
    (realGauge.gaugeRouteR' (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i)) * T2_4_3
      = ((sgn (realRepBasisParity (3 : ZMod 8) i * 0) : ℤˣ) : ℤ) •
          (T2_4_3 * (realGauge.gaugeRouteL (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8)).toAlgEquiv (cSlot ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) (realRepBasis (3 : ZMod 8) i))) := by
  have hlt : (i : ℕ) < 8 := i.isLt
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ (i : ℕ) = 4 ∨ (i : ℕ) = 5 ∨ (i : ℕ) = 6 ∨ (i : ℕ) = 7) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · rw [show i = (⟨0, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h0]; exact hintc2_4_3_0
  · rw [show i = (⟨1, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h1]; exact hintc2_4_3_1
  · rw [show i = (⟨2, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h2]; exact hintc2_4_3_2
  · rw [show i = (⟨3, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h3]; exact hintc2_4_3_3
  · rw [show i = (⟨4, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h4]; exact hintc2_4_3_4
  · rw [show i = (⟨5, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h5]; exact hintc2_4_3_5
  · rw [show i = (⟨6, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h6]; exact hintc2_4_3_6
  · rw [show i = (⟨7, by decide⟩ : Fin (realRepDim (3 : ZMod 8).val)) from Fin.ext h7]; exact hintc2_4_3_7

/-! #### Conclusion -/

/-- `gtOfT T ∈ gInterSpace` at this triple. -/
theorem gtOfT2_4_3_mem_gInterSpace :
    gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 T2_4_3 ∈ gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) 0 :=
  gtOfT_mem_interSpace_of_realRepBasis (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 hT2_4_3 hAint2_4_3 hBint2_4_3 hCint2_4_3

theorem gtOfT2_4_3_ne_zero : gtOfT ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 T2_4_3 ≠ 0 :=
  gtOfT_ne_zero ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) hsz2_4_3 T2_4_3_ne_zero

theorem gInterSpace2_4_3_ne_bot : gInterSpace ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) 0 ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, gtOfT2_4_3_mem_gInterSpace, gtOfT2_4_3_ne_zero⟩

/-- **The canonical parity at this triple**, matching the frozen certgen table. -/
theorem gParity_2_4_3 : gParity ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) = 0 :=
  (gParity_unique ℝ realGauge (2 : ZMod 8) (4 : ZMod 8) (3 : ZMod 8) gInterSpace2_4_3_ne_bot).symm

end Triple_2_4_3

end G2_8
end TripleCerts
end GaugeChi
end Superfusion

/-! ### Kernel self-check -/

#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_3_6
#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_3_7
#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_4_0
#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_4_1
#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_4_2
#print axioms Superfusion.GaugeChi.TripleCerts.G2_8.gParity_2_4_3
