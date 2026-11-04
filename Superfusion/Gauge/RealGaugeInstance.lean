/-
Superfusion / Gauge / RealGaugeInstance

Milestone M9-4c of the intrinsic gauge track: **the canonical real instance**
`realGauge : DivisionFusionGauge ℝ (ZMod 8)`, assembled from the eight real
super division representatives (`Superfusion.Gauge.RealReps`) and the `64`
landed fusion isomorphisms (`Superfusion.Gauge.RealFuse1`–`RealFuse4`).  This
is the paper's Table 1/2 realized as an honest term of the abstract skeleton
`DivisionFusionGauge` (`Superfusion.Gauge.FusionGauge`, M9-2).

**Contents.**

* `realSize : ZMod 8 → ZMod 8 → ℕ × ℕ`, the total size table, read off the
  `64` landed `realFuse_*` declarations' *produced* target sizes (not
  Table 2's — see the file docstrings of `RealFuse2`/`RealFuse4` for the
  documented deviations, all dimensionally consistent).  Implemented as a
  `ℕ → ℕ → ℕ × ℕ` case table on `(a.val, b.val)` with the two whole-row/column
  cases (`a.val = 0` or `b.val = 0`, always `1|0`) collapsed into wildcards.
* `realFuse`, the total fusion family, assembled by a genuine `64`-branch
  `match` on `(a.val, b.val)` (via the auxiliary `realFuseAux`, a `ℕ`-indexed
  total function with two `omega`-closed unreachable branches for
  `n ≥ 8`), bridged back to the `ZMod 8`-indexed statement by a single
  top-level `ZMod.val_add` rewrite (**not** repeated per branch — the
  naive "case-split first, rewrite-and-search per branch" idiom was tried
  and times out catastrophically; seeing why is the file's main technical
  note, below).
* `realGauge : DivisionFusionGauge ℝ (ZMod 8)`, the assembly.
* Smoke lemmas: field-projection `rfl`s, and light instantiations of the
  downstream abstract machinery (`DivisionFusionGauge.bwClassHom`,
  `DivisionFusionGauge.gaugeParity`) at `realGauge`, showing the pentagon
  parity apparatus genuinely fires on the canonical real instance (no
  *value* computation attempted — that is the explicit-gauge track's job).

**Technical note on the `64`-case dispatch.**  `fin_cases a` does not apply
to `a : ZMod 8` for a `Type`-valued (non-`Prop`) goal: `Fintype.elems`
membership case-splitting is implemented via `List.Mem.casesOn`, whose
recursor can only eliminate into `Prop` (confirmed empirically). The natural
fallback, `interval_cases (n := a.val)` combined with a `rw` of `(a+b).val`
into `(a.val+b.val) % 8` *before* the case split, elaborates the `64`
generated branches correctly but the *combined* term (`rw`'s `Eq.mpr`
wrapping, repeated across `64` branches glued by `<;>`, each of which
attempts *every* candidate lemma via `first | exact ... | exact ... `)
blows up: `whnf` degenerates trying to compare the large algebraic
structures pairwise across all `64 × (up to ~50)` failed alternatives,
timing out even at `maxHeartbeats 4000000`. The fix used here has two parts:
(1) push the `(a+b).val` rewrite to a *single* top-level application (so it
is never duplicated across branches), via `realFuseAux : ∀ n₁ n₂ : ℕ,
n₁ < 8 → n₂ < 8 → SuperAlgEquiv (...) (...)` stated directly in terms of
`n₁, n₂ : ℕ` (no `ZMod` casting inside); (2) make the `64`-branch dispatch a
genuine `match` term (each branch names *exactly one* candidate lemma, no
`first`-driven search), which type-checks each branch independently and
fast (confirmed: the full `64`-branch `+2`-fallback `match` compiles in a
few seconds). Every one of the `64` literal branches is a *fully concrete*
pair `(n₁, n₂)`, so the required `defeq` between `realRepAux nᵢ` and
`realRepAux (nᵢ : ZMod 8).val` is a closed, small kernel computation (no
generic-variable casting needed anywhere inside the match).

Design record: docs/paper-tables-extract.md, docs/super-track-design.md.
-/
import Superfusion.Gauge.RealFuse4
import Superfusion.Gauge.DBW
import Superfusion.Gauge.GaugePentagon
import Superfusion.Super.BWGenerator

namespace Superfusion

/-! ### The total size table -/

/-- The size table, in raw `ℕ`-indexed form (`n₁ = a.val`, `n₂ = b.val`).
The two "row `0`"/"column `0`" cases (`realFuse_zero_left`/`realFuse_zero_right`,
always `1|0`) are collapsed into wildcards; the remaining `49` cases are read
off `RealFuse1`–`RealFuse4`'s `64` landed declarations verbatim. -/
def realSizeAux : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (1, 0)
  | _, 0 => (1, 0)
  | 1, 1 => (1, 0)
  | 1, 2 => (1, 0)
  | 1, 3 => (1, 1)
  | 1, 4 => (1, 0)
  | 1, 5 => (1, 1)
  | 1, 6 => (1, 1)
  | 1, 7 => (1, 1)
  | 2, 1 => (1, 0)
  | 2, 2 => (1, 1)
  | 2, 3 => (1, 1)
  | 2, 4 => (1, 1)
  | 2, 5 => (2, 2)
  | 2, 6 => (2, 2)
  | 2, 7 => (1, 1)
  | 3, 1 => (1, 1)
  | 3, 2 => (1, 1)
  | 3, 3 => (2, 2)
  | 3, 4 => (2, 2)
  | 3, 5 => (4, 4)
  | 3, 6 => (2, 2)
  | 3, 7 => (1, 1)
  | 4, 1 => (1, 0)
  | 4, 2 => (1, 1)
  | 4, 3 => (2, 2)
  | 4, 4 => (4, 0)
  | 4, 5 => (2, 2)
  | 4, 6 => (1, 1)
  | 4, 7 => (1, 0)
  | 5, 1 => (1, 1)
  | 5, 2 => (2, 2)
  | 5, 3 => (4, 4)
  | 5, 4 => (2, 2)
  | 5, 5 => (2, 2)
  | 5, 6 => (1, 1)
  | 5, 7 => (1, 1)
  | 6, 1 => (1, 1)
  | 6, 2 => (2, 2)
  | 6, 3 => (2, 2)
  | 6, 4 => (1, 1)
  | 6, 5 => (1, 1)
  | 6, 6 => (1, 1)
  | 6, 7 => (1, 0)
  | 7, 1 => (1, 1)
  | 7, 2 => (1, 1)
  | 7, 3 => (1, 1)
  | 7, 4 => (1, 0)
  | 7, 5 => (1, 1)
  | 7, 6 => (1, 0)
  | 7, 7 => (1, 0)
  | _, _ => (0, 0)

/-- **The total size function** (M9-4c): `realSize a b = σ(a,b)`, the matrix
size at which `realRep a ᵍ⊗ realRep b` fuses onto `realRep (a+b)`. -/
def realSize (a b : ZMod 8) : ℕ × ℕ := realSizeAux a.val b.val

/-! ### The total fusion family -/

/-- **The `ℕ`-indexed core of the `64`-case dispatch**: a genuine `match` on
`(n₁, n₂) : ℕ × ℕ` with `64` concrete literal branches (each naming exactly
one landed `realFuse_*` lemma, or a literal instantiation of the
`realFuse_zero_left`/`realFuse_zero_right` families) plus two `omega`-closed
unreachable branches for `n₁ ≥ 8`/`n₂ ≥ 8`. Every branch is fully concrete,
so each `defeq` check (`realRepAux nᵢ` against `realRepAux (nᵢ : ZMod 8).val`,
etc.) is a small closed kernel computation — no generic-variable `ZMod`
casting anywhere inside. -/
noncomputable def realFuseAux (n1 n2 : ℕ) (h1 : n1 < 8) (h2 : n2 < 8) :
    SuperAlgEquiv ((realRepAux n1).gtensor (realRepAux n2))
      ((realRepAux ((n1 + n2) % 8)).matrixSuper (realSizeAux n1 n2).1
        (realSizeAux n1 n2).2) :=
  match n1, n2, h1, h2 with
  | 0, 0, _, _ => realFuse_zero_left 0
  | 0, 1, _, _ => realFuse_zero_left 1
  | 0, 2, _, _ => realFuse_zero_left 2
  | 0, 3, _, _ => realFuse_zero_left 3
  | 0, 4, _, _ => realFuse_zero_left 4
  | 0, 5, _, _ => realFuse_zero_left 5
  | 0, 6, _, _ => realFuse_zero_left 6
  | 0, 7, _, _ => realFuse_zero_left 7
  | 1, 0, _, _ => realFuse_zero_right 1
  | 2, 0, _, _ => realFuse_zero_right 2
  | 3, 0, _, _ => realFuse_zero_right 3
  | 4, 0, _, _ => realFuse_zero_right 4
  | 5, 0, _, _ => realFuse_zero_right 5
  | 6, 0, _, _ => realFuse_zero_right 6
  | 7, 0, _, _ => realFuse_zero_right 7
  | 1, 1, _, _ => realFuse_one_one
  | 1, 2, _, _ => realFuse_one_two
  | 1, 3, _, _ => realFuse_one_three
  | 1, 4, _, _ => realFuse_one_four
  | 1, 5, _, _ => realFuse_one_five
  | 1, 6, _, _ => realFuse_one_six
  | 1, 7, _, _ => realFuse_one_seven
  | 2, 1, _, _ => realFuse_two_one
  | 2, 2, _, _ => realFuse_two_two
  | 2, 3, _, _ => realFuse_two_three
  | 2, 4, _, _ => realFuse_two_four
  | 2, 5, _, _ => realFuse_two_five
  | 2, 6, _, _ => realFuse_two_six
  | 2, 7, _, _ => realFuse_two_seven
  | 3, 1, _, _ => realFuse_three_one
  | 3, 2, _, _ => realFuse_three_two
  | 3, 3, _, _ => realFuse_three_three
  | 3, 4, _, _ => realFuse_three_four
  | 3, 5, _, _ => realFuse_three_five
  | 3, 6, _, _ => realFuse_three_six
  | 3, 7, _, _ => realFuse_three_seven
  | 4, 1, _, _ => realFuse_four_one
  | 4, 2, _, _ => realFuse_four_two
  | 4, 3, _, _ => realFuse_four_three
  | 4, 4, _, _ => realFuse_four_four
  | 4, 5, _, _ => realFuse_four_five
  | 4, 6, _, _ => realFuse_four_six
  | 4, 7, _, _ => realFuse_four_seven
  | 5, 1, _, _ => realFuse_five_one
  | 5, 2, _, _ => realFuse_five_two
  | 5, 3, _, _ => realFuse_five_three
  | 5, 4, _, _ => realFuse_five_four
  | 5, 5, _, _ => realFuse_five_five
  | 5, 6, _, _ => realFuse_five_six
  | 5, 7, _, _ => realFuse_five_seven
  | 6, 1, _, _ => realFuse_six_one
  | 6, 2, _, _ => realFuse_six_two
  | 6, 3, _, _ => realFuse_six_three
  | 6, 4, _, _ => realFuse_six_four
  | 6, 5, _, _ => realFuse_six_five
  | 6, 6, _, _ => realFuse_six_six
  | 6, 7, _, _ => realFuse_six_seven
  | 7, 1, _, _ => realFuse_seven_one
  | 7, 2, _, _ => realFuse_seven_two
  | 7, 3, _, _ => realFuse_seven_three
  | 7, 4, _, _ => realFuse_seven_four
  | 7, 5, _, _ => realFuse_seven_five
  | 7, 6, _, _ => realFuse_seven_six
  | 7, 7, _, _ => realFuse_seven_seven
  | (_ + 8), _, h1, _ => absurd h1 (by omega)
  | _, (_ + 8), _, h2 => absurd h2 (by omega)

/-- **The total fusion family** (M9-4c): the `64` landed pairwise fusion
isomorphisms, assembled into a genuine total function of `(a, b) : ZMod 8 ×
ZMod 8`, via `realFuseAux` and a single top-level bridge from `(a+b).val` to
`(a.val + b.val) % 8` (`ZMod.val_add`). -/
noncomputable def realFuse (a b : ZMod 8) :
    SuperAlgEquiv ((realRep a).gtensor (realRep b))
      ((realRep (a + b)).matrixSuper (realSize a b).1 (realSize a b).2) := by
  show SuperAlgEquiv ((realRepAux a.val).gtensor (realRepAux b.val))
      ((realRepAux (a + b).val).matrixSuper (realSizeAux a.val b.val).1
        (realSizeAux a.val b.val).2)
  rw [show (a + b).val = (a.val + b.val) % 8 from ZMod.val_add a b]
  exact realFuseAux a.val b.val (ZMod.val_lt a) (ZMod.val_lt b)

/-! ### The canonical real instance -/

/-- **The canonical real division fusion gauge** (M9-4c): the paper's Table
1 (`realRep`, `Superfusion.Gauge.RealReps`) and Table 2 (`realFuse`, above)
assembled into an honest term of the abstract skeleton `DivisionFusionGauge`
(`Superfusion.Gauge.FusionGauge`, M9-2). -/
noncomputable def realGauge : DivisionFusionGauge ℝ (ZMod 8) where
  D := realRep
  central := realRep_isSuperCentral
  gradedSimple := realRep_isGradedSimple
  division := realRep_isSuperDivision
  nontriv := realRep_nontrivial
  findim := realRep_finiteDimensional
  size := realSize
  fuse := realFuse

/-! ### Smoke lemmas -/

@[simp] theorem realGauge_D (a : ZMod 8) : realGauge.D a = realRep a := rfl

@[simp] theorem realGauge_size (a b : ZMod 8) : realGauge.size a b = realSize a b := rfl

@[simp] theorem realGauge_fuse (a b : ZMod 8) : realGauge.fuse a b = realFuse a b := rfl

/-- **The Brauer–Wall class map instantiates at `realGauge`**: a genuine
homomorphism `ZMod 8 →+ Additive (BW ℝ)` (`DivisionFusionGauge.bwClassHom`,
`Superfusion.Gauge.DBW`, M9-5), no value computation attempted. -/
noncomputable def realGauge_bwClassHom : ZMod 8 →+ Additive (BW ℝ) :=
  realGauge.bwClassHom

/-- **`realGauge`'s class of the top floor is the paper's generator
`[D₁] ∈ BW(ℝ)`** (`Superfusion.Super.BWGenerator.bwGenReal`): `realRep 7 =
divisionTower 1 1` definitionally (`realRepAux`'s last clause), so `realGauge
.bwClass 7 = BW.ofAzumaya (divisionTower 1 1) = bwGen 1 one_ne_zero =
bwGenReal` is a genuine `rfl` (both `IsSuperAzumaya` witnesses are proofs of
a `Prop`, hence defeq by proof irrelevance) — connecting the new gauge-level
class map to the previously-landed orderOf-8 world (`bwGenReal_pow_eight`,
`orderOf_bwGenReal_dvd_eight`, M7f-4d). -/
theorem realGauge_bwClass_seven : realGauge.bwClass 7 = bwGenReal := rfl

/-- **The abstract pentagon-parity machinery instantiates at `realGauge`**:
a genuine function `(ZMod 8)³ → ZMod 2` (`DivisionFusionGauge.gaugeParity`,
`Superfusion.Gauge.GaugePentagon`, M9-3b), demonstrating that the pentagon
apparatus fires on the canonical real instance. No parity *value* is
computed here — that needs the explicit-gauge project. -/
noncomputable def realGauge_gaugeParity : ZMod 8 → ZMod 8 → ZMod 8 → ZMod 2 :=
  realGauge.gaugeParity

/-- Likewise, the extracted route-comparison intertwiner
`DivisionFusionGauge.gaugePentagonT` instantiates at `realGauge`, at every
triple `(a, b, c)`, landing in the corresponding composite matrix frame. -/
noncomputable def realGauge_gaugePentagonT (a b c : ZMod 8) :
    ((realGauge.D (a + b + c)).matrixSuper (realGauge.gaugeSizeL a b c).1
      (realGauge.gaugeSizeL a b c).2).carrier :=
  realGauge.gaugePentagonT a b c

end Superfusion
