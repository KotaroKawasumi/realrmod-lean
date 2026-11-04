/-
Superfusion / Gauge / GaugeRoutes

Milestone M9-3a of the intrinsic gauge track: **gauge-level fusion routes and
the frame alignment** — the first port of the concrete comparison theory
(`Superfusion.Super.PentagonRoutes`'s `routeL`/`routeR`) to an abstract
`DivisionFusionGauge K G` (`Superfusion.Gauge.FusionGauge`).

**Contents:**

* **Index/frame transport** (`gaugeCast`, `gaugeMatrixCast`): for an
  *abstract* group `G`, `a + (b + c) ≠ (a + b) + c` *definitionally* (unlike
  `ZMod 8`'s literal-parse equality, where `PentagonRoutes.stdMatrixCast` is
  almost decorative) — these casts are load-bearing everywhere below.
* **Composite sizes** `gaugeSizeL`/`gaugeSizeR`, literal ports of
  `PentagonRoutes.sizeL`/`sizeR` through `Γ.size`.
* **The two routes at their natural frames**: `gaugeRouteL` (landing at
  `(a+b)+c`, size `gaugeSizeL`, exactly `routeL`'s composite) and
  `gaugeRouteR` (landing at `a+(b+c)`, size `gaugeSizeR`, `routeR`'s
  composite *without* the final cast — unlike the concrete `ZMod 8` case,
  there the two natural frames need not coincide here).
* **The swap equivalence** `matrixSuperSwap`: `M_{p|q}(P) ≅ M_{q|p}(P)`, by
  reindexing along `Sum.swap`.
* **The frame alignment** `frameAlign`: a *route-independent* comparison
  `M_{gaugeSizeR}(D_{a+b+c}) ≅ M_{gaugeSizeL}(D_{a+b+c})` (both sizes read at
  the *same* index `(a+b)+c`, `gaugeSizeR` having been transported there by
  `gaugeMatrixCast`), built by case analysis on how the two size pairs
  compare (equal / swapped / neither), with the third case forced into the
  odd-unit collapse. The two size-rigidity theorems
  (`Superfusion.Gauge.SizeRigidity`) show the case split is exhaustive, via
  a *witness* isomorphism assembled from the routes — used only inside the
  exhaustiveness proof, never as `frameAlign`'s returned data (see
  `frameAlign`'s docstring for why).
* **The aligned right route** `gaugeRouteR'`, the gauge analogue of the
  concrete `routeR` (which had its cast built in): `gaugeRouteR` composed
  with the transport to `(a+b)+c` and `frameAlign`, landing at exactly
  `gaugeRouteL`'s target — ready for the Skolem–Noether comparison of
  M9-3b.
-/
import Superfusion.Gauge.FusionGauge
import Superfusion.Super.MatrixSuperTensor
import Superfusion.Super.TensorCoherence
import Superfusion.Super.SuperAlgEquivGradedHom

namespace Superfusion

/-! ### The swap equivalence `M_{p|q}(P) ≅ M_{q|p}(P)` -/

section MatrixSwap

variable {K : Type*} [CommRing K]

/-- **The checkerboard parity shifts by `1` under `Sum.swap`** (on the index
type `Fin p ⊕ Fin q`, landing in `Fin q ⊕ Fin p`): the "first block" and
"second block" roles trade places, so a point of parity `0` becomes parity
`1` and vice versa. -/
private theorem sumParity_swap (p q : ℕ) (x : Fin p ⊕ Fin q) :
    sumParity q p (Sum.swap x) = sumParity p q x + 1 := by
  rcases x with a | a
  · show (1 : ZMod 2) = 0 + 1
    decide
  · show (0 : ZMod 2) = 1 + 1
    decide

/-- Pure `ZMod 2` arithmetic: a shift of `1` on *both* summands of an entry
degree `i + x + y` cancels, since `1 + 1 = 0`. -/
private theorem zmod2_swap_cancel (i x y : ZMod 2) :
    i + (x + 1) + (y + 1) = i + x + y := by
  decide +revert

/-- **The swap equivalence**: `M_{p|q}(P) ≅ M_{q|p}(P)`, by reindexing along
`Sum.swap` (`Equiv.sumComm`). The checkerboard parity function shifts by
`+1` on *both* the row and column index under the swap (`sumParity_swap`),
so the total entry degree `i + π(row) + π(col)` is unchanged
(`zmod2_swap_cancel`): the plain reindex is grading-preserving, hence an
algebra isomorphism carrying the checkerboard grading onto the checkerboard
grading of the swapped shape. -/
noncomputable def matrixSuperSwap (P : SuperAlgebra K) (p q : ℕ) :
    SuperAlgEquiv (P.matrixSuper p q) (P.matrixSuper q p) :=
  ⟨Matrix.reindexAlgEquiv K P.carrier (Equiv.sumComm (Fin p) (Fin q)), fun i => by
    show (matrixGradingA (sumParity p q) P.grading i).map
        (Matrix.reindexAlgEquiv K P.carrier (Equiv.sumComm (Fin p) (Fin q))).toLinearMap
      = matrixGradingA (sumParity q p) P.grading i
    ext N
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨M, hM, rfl⟩
      intro a b
      show (Matrix.reindexAlgEquiv K P.carrier (Equiv.sumComm (Fin p) (Fin q))) M a b
        ∈ P.grading (i + sumParity q p a + sumParity q p b)
      rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
      have h := hM (Sum.swap a) (Sum.swap b)
      rwa [sumParity_swap q p a, sumParity_swap q p b, zmod2_swap_cancel] at h
    · intro hN
      refine ⟨(Matrix.reindexAlgEquiv K P.carrier (Equiv.sumComm (Fin p) (Fin q))).symm N,
        fun a b => ?_, ?_⟩
      · show (Matrix.reindexAlgEquiv K P.carrier (Equiv.sumComm (Fin p) (Fin q))).symm N a b
          ∈ P.grading (i + sumParity p q a + sumParity p q b)
        rw [Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
          Matrix.submatrix_apply]
        have h := hN (Sum.swap a) (Sum.swap b)
        rwa [sumParity_swap p q a, sumParity_swap p q b, zmod2_swap_cancel] at h
      · exact (Matrix.reindexAlgEquiv K P.carrier
          (Equiv.sumComm (Fin p) (Fin q))).apply_symm_apply N⟩

end MatrixSwap

namespace DivisionFusionGauge

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)] {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

/-! ### Index transport -/

/-- **Index transport**: `D_x ≅ D_y` along an index equality, by `subst`.
For an abstract `[AddGroup G]`, index equalities such as `a + (b + c) =
(a + b) + c` are *not* definitional (unlike `ZMod 8`'s literal-parse
equality), so this cast is genuinely load-bearing throughout the routes
below. -/
def gaugeCast {x y : G} (h : x = y) : SuperAlgEquiv (Γ.D x) (Γ.D y) :=
  superAlgebraFamilyCast Γ.D h

/-- The index cast along reflexivity is the identity graded algebra
equivalence. -/
@[simp]
theorem gaugeCast_refl (x : G) :
    Γ.gaugeCast (rfl : x = x) = SuperAlgEquiv.refl (Γ.D x) :=
  rfl

/-- Successive index casts compose to the cast along transitivity. -/
@[simp]
theorem gaugeCast_trans {x y z : G} (h₁ : x = y) (h₂ : y = z) :
    (Γ.gaugeCast h₁).trans (Γ.gaugeCast h₂) =
      Γ.gaugeCast (h₁.trans h₂) := by
  subst h₁
  subst h₂
  rfl

/-- The inverse of an index cast is the cast along the symmetric
equality. -/
@[simp]
theorem gaugeCast_symm {x y : G} (h : x = y) :
    (Γ.gaugeCast h).symm = Γ.gaugeCast h.symm := by
  subst h
  rfl

/-- Reflexive index transport acts identically on coefficients. -/
theorem gaugeCast_refl_apply (x : G) (τ : (Γ.D x).carrier) :
    (Γ.gaugeCast (rfl : x = x)).toAlgEquiv τ = τ :=
  rfl

/-- The coefficientwise form of `gaugeCast_trans`. -/
@[simp]
theorem gaugeCast_trans_apply {x y z : G} (h₁ : x = y) (h₂ : y = z)
    (τ : (Γ.D x).carrier) :
    (Γ.gaugeCast h₂).toAlgEquiv ((Γ.gaugeCast h₁).toAlgEquiv τ) =
      (Γ.gaugeCast (h₁.trans h₂)).toAlgEquiv τ := by
  subst h₁
  subst h₂
  rfl

/-- The coefficientwise form of `gaugeCast_symm`. -/
@[simp]
theorem gaugeCast_symm_apply {x y : G} (h : x = y)
    (τ : (Γ.D y).carrier) :
    (Γ.gaugeCast h).toAlgEquiv.symm τ =
      (Γ.gaugeCast h.symm).toAlgEquiv τ := by
  subst h
  rfl

/-- Index transport preserves the homogeneous degree of a coefficient. -/
theorem gaugeCast_mem_grading {x y : G} (h : x = y)
    {i : ZMod 2} {τ : (Γ.D x).carrier}
    (hτ : τ ∈ (Γ.D x).grading i) :
    (Γ.gaugeCast h).toAlgEquiv τ ∈ (Γ.D y).grading i :=
  (Γ.gaugeCast h).map_mem_grading hτ

/-- The matrix-frame version of `gaugeCast`: transport along both an index
equality and a size equality, `subst`-based and hence `rfl`-transparent
once the two equalities are supplied. Mirrors `PentagonRoutes.stdMatrixCast`
exactly. -/
noncomputable def gaugeMatrixCast {x y : G} (h : x = y) {s t : ℕ × ℕ} (hs : s = t) :
    SuperAlgEquiv ((Γ.D x).matrixSuper s.1 s.2) ((Γ.D y).matrixSuper t.1 t.2) := by
  subst h
  subst hs
  exact SuperAlgEquiv.refl _

/-! ### Composite sizes -/

/-- The composed matrix size of the left route (outer `Γ.size a b` applied
to inner `Γ.size (a+b) c`, in `matrixSuperComp`'s convention). Literal port
of `PentagonRoutes.sizeL`. -/
def gaugeSizeL (a b c : G) : ℕ × ℕ :=
  ((Γ.size a b).1 * (Γ.size (a + b) c).1 + (Γ.size a b).2 * (Γ.size (a + b) c).2,
    (Γ.size a b).1 * (Γ.size (a + b) c).2 + (Γ.size a b).2 * (Γ.size (a + b) c).1)

/-- The composed matrix size of the right route. Literal port of
`PentagonRoutes.sizeR`. -/
def gaugeSizeR (a b c : G) : ℕ × ℕ :=
  ((Γ.size b c).1 * (Γ.size a (b + c)).1 + (Γ.size b c).2 * (Γ.size a (b + c)).2,
    (Γ.size b c).1 * (Γ.size a (b + c)).2 + (Γ.size b c).2 * (Γ.size a (b + c)).1)

/-! ### The two routes at their natural frames -/

/-- **The left fusion route**, at its natural frame: `(D_a ᵍ⊗ D_b) ᵍ⊗ D_c ≅
M_{σ}(D_{(a+b)+c})` through `(ab)c`. Literal port of `PentagonRoutes.routeL`. -/
noncomputable def gaugeRouteL (a b c : G) :
    SuperAlgEquiv (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c))
      ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2) :=
  ((Γ.fuse a b).gtensorCongr (SuperAlgEquiv.refl (Γ.D c))).trans
    ((matrixSuperGtensor (Γ.D (a + b)) (Γ.D c) (Γ.size a b).1 (Γ.size a b).2).trans
      (((Γ.fuse (a + b) c).matrixSuper (Γ.size a b).1 (Γ.size a b).2).trans
        (matrixSuperComp (Γ.D (a + b + c)) (Γ.size a b).1 (Γ.size a b).2
          (Γ.size (a + b) c).1 (Γ.size (a + b) c).2)))

/-- **The right fusion route**, at its natural frame `a + (b + c)` and
natural size `gaugeSizeR` — unlike `PentagonRoutes.routeR`, no final cast
is applied here: for an abstract `G` there is (a priori) no reason for the
two natural frames `(a+b)+c` and `a+(b+c)`, nor the two natural sizes, to
line up, so the comparison is deferred to `frameAlign`/`gaugeRouteR'`. -/
noncomputable def gaugeRouteR (a b c : G) :
    SuperAlgEquiv (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c))
      ((Γ.D (a + (b + c))).matrixSuper (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2) :=
  (gtensorAssoc (Γ.D a) (Γ.D b) (Γ.D c)).trans
    (((SuperAlgEquiv.refl (Γ.D a)).gtensorCongr (Γ.fuse b c)).trans
      ((matrixSuperGtensorRight (Γ.D a) (Γ.D (b + c)) (Γ.size b c).1 (Γ.size b c).2).trans
        (((Γ.fuse a (b + c)).matrixSuper (Γ.size b c).1 (Γ.size b c).2).trans
          (matrixSuperComp (Γ.D (a + (b + c))) (Γ.size b c).1 (Γ.size b c).2
            (Γ.size a (b + c)).1 (Γ.size a (b + c)).2))))

/-! ### The frame alignment -/

/-- **The frame alignment** (M9-3a): a *route-independent* comparison of
the two natural matrix frames of the composite `D_{(a+b)+c}`, transported
onto the common index `(a+b)+c` (`gaugeSizeR` read there via
`gaugeMatrixCast`, matching the first step of `gaugeRouteR'`).

Constructed by case analysis on how the unordered pair `gaugeSizeR` compares
to `gaugeSizeL`:

1. equal as ordered pairs — `gaugeMatrixCast`;
2. equal up to swap — `matrixSuperSwap` then `gaugeMatrixCast`;
3. otherwise — forced into the **odd-unit collapse**
   (`matrixSuperOddCollapse`) onto the common total size `(p+q \| 0)` on
   both sides.

**Why case 3 is forced, and why the total sizes agree in it** (the
exhaustiveness argument): assemble a *witness* isomorphism
`M_{gaugeSizeR}(D) ≅ M_{gaugeSizeL}(D)` from the two routes themselves —
`gaugeRouteR` transported to the common index, inverted, then composed with
`gaugeRouteL` — and feed it to the two size-rigidity theorems
(`Superfusion.Gauge.SizeRigidity`): `sizeRigidity_total` gives the total
size equality needed for the case-3 collapse cast *unconditionally*, and
`sizeRigidity_even`, contraposed, shows that if neither case 1 nor case 2
holds then `D_{(a+b)+c}` cannot be purely even, so the type dichotomy
(`Bimod.IsSuperDivision.dichotomy`) hands us an odd unit.

This witness isomorphism is used **only inside the exhaustiveness proof**,
never as `frameAlign`'s returned value: building the alignment itself out
of the routes would make it definitionally tied to them, collapsing the
later Skolem–Noether comparison between `gaugeRouteL` and `gaugeRouteR'` to
a triviality (`frameAlign` needs to be data *independent* of the routes for
that comparison to carry content). -/
noncomputable def frameAlign (a b c : G) :
    SuperAlgEquiv ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2)
      ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2) := by
  classical
  haveI := Γ.nontriv (a + b + c)
  haveI := Γ.findim (a + b + c)
  by_cases h1 : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c
  · exact Γ.gaugeMatrixCast rfl h1
  by_cases h2 : Γ.gaugeSizeR a b c = (Γ.gaugeSizeL a b c).swap
  · have hs : ((Γ.gaugeSizeR a b c).2, (Γ.gaugeSizeR a b c).1) = Γ.gaugeSizeL a b c := by
      rw [h2]; exact Prod.swap_swap _
    exact (matrixSuperSwap (Γ.D (a + b + c)) (Γ.gaugeSizeR a b c).1
        (Γ.gaugeSizeR a b c).2).trans (Γ.gaugeMatrixCast rfl hs)
  · -- The witness isomorphism, used only to extract the numeric facts below.
    have eIso : SuperAlgEquiv
        ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2)
        ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2) :=
      ((Γ.gaugeRouteR a b c).trans
          (Γ.gaugeMatrixCast (add_assoc a b c).symm rfl)).symm.trans (Γ.gaugeRouteL a b c)
    have htot : (Γ.gaugeSizeR a b c).1 + (Γ.gaugeSizeR a b c).2
        = (Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2 := sizeRigidity_total eIso
    have hnoteven : ¬ (Γ.D (a + b + c)).grading 1 = ⊥ := by
      intro heven
      rcases sizeRigidity_even heven eIso with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h1 (Prod.ext e1 e2)
      · exact h2 (Prod.ext e1 e2)
    have hex := (Γ.division (a + b + c)).dichotomy.resolve_left hnoteven
    set w := hex.choose with hw_def
    have hw1 : w ∈ (Γ.D (a + b + c)).grading 1 := hex.choose_spec.1
    have hw : IsUnit w := hex.choose_spec.2
    exact (matrixSuperOddCollapse (Γ.D (a + b + c)) (Γ.gaugeSizeR a b c).1
        (Γ.gaugeSizeR a b c).2 hw1 hw).trans
      ((Γ.gaugeMatrixCast rfl (show
          ((Γ.gaugeSizeR a b c).1 + (Γ.gaugeSizeR a b c).2, 0)
            = ((Γ.gaugeSizeL a b c).1 + (Γ.gaugeSizeL a b c).2, 0) from by
        rw [htot])).trans
        (matrixSuperOddCollapse (Γ.D (a + b + c)) (Γ.gaugeSizeL a b c).1
          (Γ.gaugeSizeL a b c).2 hw1 hw).symm)

/-- **The aligned right route** (M9-3a): the gauge analogue of the concrete
`PentagonRoutes.routeR` (which had its comparison cast built in) — transport
`gaugeRouteR` to the common index `(a+b)+c`, then align frames, landing at
exactly `gaugeRouteL`'s target. Ready for the Skolem–Noether route
comparison of M9-3b. -/
noncomputable def gaugeRouteR' (a b c : G) :
    SuperAlgEquiv (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c))
      ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2) :=
  ((Γ.gaugeRouteR a b c).trans
      (Γ.gaugeMatrixCast (add_assoc a b c).symm rfl)).trans (Γ.frameAlign a b c)

end DivisionFusionGauge

end Superfusion
