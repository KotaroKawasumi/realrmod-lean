/-
Superfusion / Bimod / ChiTower

Milestone M8a-8d′-iii-b (roadmap v3, FINAL round): **the dimension
arithmetic and the discharge** — `chiTower`, the pentagon scalar of
the standard ℤ/8 tower model, with NO one-dimensionality assumption:
it is now a *theorem*, not a hypothesis, given only invertible
triple-intertwiner data.

1. **`finrank K Q1 = quadEnvSize K a b c d`.**  `TowerColumn K x y` is
   literally the function type `fuseIdx x y → T_{x+y}`, so
   `RelTensor.freeCollapse` (`FreeCollapse.lean`) applies to
   `B_L = C_{a,b} ⊗[T_{a+b}] C_{a+b,c}` directly, collapsing it to
   `fuseIdx a b → C_{a+b,c}`; a further currying identifies this with
   `(fuseIdx a b × fuseIdx (a+b) c) → T_{a+b+c}`, of `freeCollapse`'s
   shape again, so `Q1 = B_L ⊗[T_{a+b+c}] C_{a+b+c,d}` collapses to
   `(fuseIdx a b × fuseIdx (a+b) c) → C_{a+b+c,d}`.  Both collapses
   respect the outer right `T_{a+b+c}`-action (`RelTensor.freeCollapse`
   intertwines any further commuting right action, a direct
   `RelTensor.induction_on` fact — no linearity/`hom_ext` bookkeeping
   needed, since both sides are literal equalities of elements), so
   the composite is a `LinearEquiv` via `RelTensor.mapEquivLeft`.
   Counting dimensions with `Module.finrank_pi_fintype` on each level
   and matching against `quadEnvSize`'s own definition (`extSize`,
   `sizeL`, `fuseSize` unfold to the same product of `Fintype.card`s,
   by `ring` on the underlying `ℕ`-arithmetic) gives the equality.

2. **`finrank K Q4 = finrank K Q1`, the shortcut.**  Rather than
   repeating the collapse for `Q4`'s own (differently-associated)
   presentation, `botRoute`'s bijectivity (`ChiAbs.lean`'s
   `botRoute_bijective`, for invertible `t₄`, `t₅`) already supplies a
   `LinearEquiv Q1 ≃ₗ[K] Q4` directly — `LinearEquiv.finrank_eq` closes
   the gap for free.

3. **The discharge.** `hspanTower`: assembling
   `mem_quadInterSpace_iff_gradedHomF` (both uses),
   `gradedHomF_finrank_sum_le_one` (via `quadEnvSplit`/`quadEnvSize`
   and deliverables 1–2), `parityConcentration`/
   `spanning_of_finrank_le_one`, `botRoute_mem`, and
   `botRoute_ne_zero_of_bijective` (`Nontrivial Q1` from
   `finrank K Q1 = quadEnvSize ≠ 0`).

4. **`chiTower`.**  The pentagon scalar of the standard tower model,
   for a quadruple `(a, b, c, d)` and invertible triple-intertwiner
   data at every one of the five edges (`φ₁`–`φ₅`, each bundled with
   its `interSpace` membership at a declared degree, except `φ₂`
   — `Q2rInner`/`Q3Inner` carry no such bundle, so its four extra
   conditions are taken raw, exactly as `QuadMembership2.lean`'s
   `topRoute_mem` already requires) and a common-degree hypothesis
   `he : e₁ + e₂ + e₃ = e₄ + e₅` — defined via `chiAbs`, with
   `chiTower_spec` (`topRoute = chiTower • botRoute`) and
   `chiTower_ne_zero` (from `topRoute`'s bijectivity).  This
   identifies the paper's `χ` for the standard tower model over any
   field with `2` invertible, with no one-dimensionality assumption; the
   identification with the concrete `pentagonChi` and the canonicity of
   the `t`'s is M8a-9.
-/
import Superfusion.Bimod.QuadInterface2
import Superfusion.Bimod.FreeCollapse

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### General layer: `freeCollapse` intertwines a further commuting
right action, and the currying of a nested Pi type -/

section FreeCollapseRight

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable {C : Type*} [Ring C] [Algebra K C]
variable [Module Cᵐᵒᵖ N] [SMulCommClass A Cᵐᵒᵖ N] [IsScalarTower K Cᵐᵒᵖ N]

/-- **`freeCollapse` intertwines a further commuting right `C`-action**:
for `N` carrying a right `C`-action commuting with the balancing left
`A`-action, `freeCollapse` sends the outer right action
(`rightActionEnd`, descended from `N`'s own action) to the pointwise
right action on the collapsed column `n → N`.  Proved directly by
`RelTensor.induction_on` — both sides are literal equalities of
elements, so no `hom_ext`/linearity bookkeeping (and hence no
`SMulCommClass _ K _` worries) is needed. -/
theorem RelTensor.freeCollapse_rightActionEnd (c : Cᵐᵒᵖ) (x : (n → A) ⊗[A;K] N) :
    RelTensor.freeCollapse (rightActionEnd K A (n → A) N c x)
      = c • RelTensor.freeCollapse x := by
  induction x using RelTensor.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | mk v w =>
      rw [rightActionEnd_mk, RelTensor.freeCollapse_mk, RelTensor.freeCollapse_mk]
      funext j
      rw [Pi.smul_apply, smul_comm]
  | add x y hx hy => rw [map_add, map_add, map_add, smul_add, hx, hy]

end FreeCollapseRight

section PiProd

variable (K : Type*) [Field K]
variable (n₁ n₂ : Type*) (T : Type*) [AddCommMonoid T] [Module K T]

/-- **Currying a nested Pi type over a product index**, as a
`LinearEquiv`: `(n₁ → n₂ → T) ≃ₗ[K] (n₁ × n₂ → T)`. -/
def piProdCollapse : (n₁ → n₂ → T) ≃ₗ[K] (n₁ × n₂ → T) where
  toFun f p := f p.1 p.2
  invFun g i j := g (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end PiProd

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### The `fuseIdx` cardinality bridge -/

theorem card_fuseIdx (x y : ZMod 8) :
    Fintype.card (fuseIdx x y) = (fuseSize x y).1 + (fuseSize x y).2 := by
  show Fintype.card (Fin (fuseSize x y).1 ⊕ Fin (fuseSize x y).2) = _
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-! ### `finrank K Q1 = quadEnvSize K a b c d`: the `freeCollapse`
iteration -/

/-- **`B_L`'s own `freeCollapse`, transported along the outer right
`T_{a+b+c}`-action**: the general `RelTensor.freeCollapse_rightActionEnd`
instantiated at `B_L`'s construction (`BL.right_smul_apply` bridges the
registered right action to the generic `rightActionEnd` spelling). -/
theorem freeCollapse_BL_rightEquiv (τ : (stdTower (K := K) (a + b + c)).carrier)
    (m : BL K a b c) :
    RelTensor.freeCollapse (MulOpposite.op τ • m)
      = MulOpposite.op τ • RelTensor.freeCollapse m := by
  have h := RelTensor.freeCollapse_rightActionEnd (K := K)
    (A := (stdTower (K := K) (a + b)).carrier) (n := fuseIdx a b)
    (N := TowerColumn K (a + b) c) (C := (stdTower (K := K) (a + b + c)).carrier)
    (MulOpposite.op τ) m
  rw [BL.right_smul_apply]
  exact h

/-- **The first collapse**: `B_L = C_{a,b} ⊗[T_{a+b}] C_{a+b,c} ≅
(fuseIdx a b × fuseIdx (a+b) c) → T_{a+b+c}` — `freeCollapse` followed
by currying the resulting `fuseIdx a b → (fuseIdx (a+b) c → T_{a+b+c})`
(the literal unfolding of `fuseIdx a b → C_{a+b,c}`). -/
noncomputable def q1FirstCollapse :
    BL K a b c ≃ₗ[K]
      (fuseIdx a b × fuseIdx (a + b) c → (stdTower (K := K) (a + b + c)).carrier) :=
  RelTensor.freeCollapse.trans
    (piProdCollapse K (fuseIdx a b) (fuseIdx (a + b) c)
      (stdTower (K := K) (a + b + c)).carrier)

/-- **`q1FirstCollapse`'s generator formula**: it computes `freeCollapse`
followed by the literal `Prod.fst`/`Prod.snd` uncurrying — `rfl`, since
`.trans` and `piProdCollapse` are both function composition at the
`toFun` level. -/
theorem q1FirstCollapse_apply (m : BL K a b c) (p : fuseIdx a b × fuseIdx (a + b) c) :
    q1FirstCollapse K a b c m p = RelTensor.freeCollapse m p.1 p.2 := rfl

/-- **`q1FirstCollapse` intertwines the outer right `T_{a+b+c}`-action**
(the pointwise action on the product-indexed column). -/
theorem q1FirstCollapse_rightEquiv (τ : (stdTower (K := K) (a + b + c)).carrier)
    (m : BL K a b c) :
    q1FirstCollapse K a b c (MulOpposite.op τ • m)
      = MulOpposite.op τ • q1FirstCollapse K a b c m := by
  funext p
  show RelTensor.freeCollapse (MulOpposite.op τ • m) p.1 p.2
    = MulOpposite.op τ • RelTensor.freeCollapse m p.1 p.2
  exact congrFun (congrFun (freeCollapse_BL_rightEquiv K a b c τ m) p.1) p.2

/-- **`Q1` collapses to a column over the product index**:
`Q1 = B_L ⊗[T_{a+b+c}] C_{a+b+c,d} ≅ (fuseIdx a b × fuseIdx (a+b) c) →
C_{a+b+c,d}` — transport `B_L`'s first collapse along the outer
`RelTensor` (`RelTensor.mapEquivLeft`), then collapse the (now literally
column-shaped) result with `freeCollapse` again. -/
noncomputable def q1Collapse :
    Q1 K a b c d ≃ₗ[K]
      (fuseIdx a b × fuseIdx (a + b) c → TowerColumn K (a + b + c) d) :=
  (RelTensor.mapEquivLeft K (q1FirstCollapse K a b c) (q1FirstCollapse_rightEquiv K a b c)).trans
    RelTensor.freeCollapse

omit [Invertible (2 : K)] in
/-- **`finrank K (n → M) = Fintype.card n * finrank K M`** for a
`Fintype n` and finite-dimensional `M` (the constant-family case of
`Module.finrank_pi_fintype`). -/
private theorem finrank_pi_const {M : Type*} [AddCommGroup M] [Module K M]
    [Module.Finite K M] (n : Type*) [Fintype n] :
    Module.finrank K (n → M) = Fintype.card n * Module.finrank K M := by
  rw [Module.finrank_pi_fintype K, Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [Invertible (2 : K)] in
/-- **The `K`-dimension of a tower column**: `finrank K C_{x,y} =
Fintype.card (fuseIdx x y) * finrank K T_{x+y}`. -/
theorem finrank_towerColumn (x y : ZMod 8) :
    Module.finrank K (TowerColumn K x y)
      = Fintype.card (fuseIdx x y) * Module.finrank K (stdTower (K := K) (x + y)).carrier := by
  show Module.finrank K (fuseIdx x y → (stdTower (K := K) (x + y)).carrier) = _
  exact finrank_pi_const K (fuseIdx x y)

omit [Invertible (2 : K)] in
/-- **`quadEnvSize`'s value, unfolded to the `fuseIdx`/tower-rank
product**: `quadEnvSize` is (by its own definition, `QuadEnvelope.lean`)
the `Fintype.card` of `(extSize (sizeL a b c) (a+b+c) d)`'s index times
`finrank K T_{a+b+c+d}`; unfolding `extSize`/`sizeL`/`fuseSize` (all
public `def`s) and matching `Fintype.card (fuseIdx x y) = (fuseSize x
y).1 + (fuseSize x y).2` reduces this to a plain `ℕ`-arithmetic identity
(`ring`, treating the `fuseSize` pairs as atoms). -/
theorem quadEnvSize_eq :
    quadEnvSize K a b c d
      = Fintype.card (fuseIdx a b) * Fintype.card (fuseIdx (a + b) c) *
          Fintype.card (fuseIdx (a + b + c) d) *
          Module.finrank K (stdTower (K := K) (a + b + c + d)).carrier := by
  show Fintype.card
      ((Fin (extSize (sizeL a b c) (a + b + c) d).1 ⊕
          Fin (extSize (sizeL a b c) (a + b + c) d).2)
        × Fin (Module.finrank K (stdTower (K := K) (a + b + c + d)).carrier))
      = _
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, card_fuseIdx, card_fuseIdx, card_fuseIdx]
  show ((extSize (sizeL a b c) (a + b + c) d).1 + (extSize (sizeL a b c) (a + b + c) d).2)
      * Module.finrank K (stdTower (K := K) (a + b + c + d)).carrier
    = ((fuseSize a b).1 + (fuseSize a b).2) * ((fuseSize (a + b) c).1 + (fuseSize (a + b) c).2) *
        ((fuseSize (a + b + c) d).1 + (fuseSize (a + b + c) d).2) *
        Module.finrank K (stdTower (K := K) (a + b + c + d)).carrier
  unfold extSize sizeL
  ring

/-- **`finrank K Q1 = quadEnvSize K a b c d`** (deliverable 1). -/
theorem finrank_Q1_eq_quadEnvSize :
    Module.finrank K (Q1 K a b c d) = quadEnvSize K a b c d := by
  rw [(q1Collapse K a b c d).finrank_eq, quadEnvSize_eq]
  haveI : Module.Finite K (TowerColumn K (a + b + c) d) :=
    inferInstanceAs (Module.Finite K
      (fuseIdx (a + b + c) d → (stdTower (K := K) (a + b + c + d)).carrier))
  rw [finrank_pi_const K (fuseIdx a b × fuseIdx (a + b) c), Fintype.card_prod,
    finrank_towerColumn]
  ring

/-- **`Q1` is finite-dimensional** (transported off the collapse chain,
`q1Collapse`, from the finite `TowerColumn`/tower-rank data). -/
theorem q1_finite : Module.Finite K (Q1 K a b c d) := by
  haveI : Module.Finite K (TowerColumn K (a + b + c) d) :=
    inferInstanceAs (Module.Finite K
      (fuseIdx (a + b + c) d → (stdTower (K := K) (a + b + c + d)).carrier))
  exact Module.Finite.equiv (q1Collapse K a b c d).symm

/-- **`Q1` is nontrivial**: `finrank K Q1 = quadEnvSize K a b c d ≠ 0`. -/
theorem q1_nontrivial : Nontrivial (Q1 K a b c d) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [finrank_Q1_eq_quadEnvSize]
  exact Nat.pos_of_ne_zero (quadEnvSize_ne_zero K a b c d)

/-- **`finrank K Q4 = quadEnvSize K a b c d`** (deliverable 1's `Q4`
route, the cheaper shortcut noted in the design: `botRoute`'s own
bijectivity, for invertible `t₄`, `t₅`, already supplies a `LinearEquiv
Q1 ≃ₗ[K] Q4` — no separate collapse of `Q4`'s own presentation is
needed). -/
theorem finrank_Q4_eq_quadEnvSize
    {e₄ : ZMod 2} (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
        t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
    {e₅ : ZMod 2} (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
        t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))
    (hbij : Function.Bijective (botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅)) :
    Module.finrank K (Q4 K a b c d) = quadEnvSize K a b c d := by
  haveI := q1_finite K a b c d
  rw [← finrank_Q1_eq_quadEnvSize,
    (LinearEquiv.ofBijective (botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅) hbij).finrank_eq]

/-! ### The discharge -/

/-- **The discharge**: for invertible `t₄`, `t₅` (with their full
`interSpace` membership, at declared degrees `e₄`, `e₅`), every element
of `quadInterSpace K a b c d (e₄ + e₅)` is a scalar multiple of
`botRoute` — the Schur-type spanning hypothesis `chiAbs`/`ChiAbs.lean`
consumes as `hspan`, now a THEOREM (no one-dimensionality assumption):
assembled from `mem_quadInterSpace_iff_gradedHomF` (both uses),
`gradedHomF_finrank_sum_le_one` (deliverables 1–2, via `quadEnvSplit`/
`quadEnvSize`), `parityConcentration`, and `botRoute_mem` +
`botRoute_ne_zero_of_bijective` (`Nontrivial Q1` from
`finrank K Q1 = quadEnvSize ≠ 0`). -/
theorem hspanTower
    {e₄ : ZMod 2} (φ₄ : BL K (a + b) c d ≃ₗ[K] BR K (a + b) c d)
    (ht4 : φ₄.toLinearMap ∈ interSpace K (a + b) c d e₄)
    {e₅ : ZMod 2} (φ₅ : BL K a b (c + d) ≃ₗ[K] BR K a b (c + d))
    (ht5 : φ₅.toLinearMap ∈ interSpace K a b (c + d) e₅) :
    ∀ f ∈ quadInterSpace K a b c d (e₄ + e₅),
      ∃ cc : K, f = cc • botRoute K a b c d e₄ φ₄.toLinearMap
        ((mem_superEquivariant (stdTower (K := K) (a + b)).grading).mp
          ((mem_interSpace_iff K (a + b) c d).mp ht4).2.1)
        e₅ φ₅.toLinearMap
        ((mem_superEquivariant (stdTower (K := K) (c + d)).grading).mp
          ((mem_interSpace_iff K a b (c + d)).mp ht5).2.2.2.1) := by
  have hφ₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
        φ₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • φ₄ n) :=
    (mem_superEquivariant (stdTower (K := K) (a + b)).grading).mp
      ((mem_interSpace_iff K (a + b) c d).mp ht4).2.1
  have hφ₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
        φ₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • φ₅ n) :=
    (mem_superEquivariant (stdTower (K := K) (c + d)).grading).mp
      ((mem_interSpace_iff K a b (c + d)).mp ht5).2.2.2.1
  haveI := q1_finite K a b c d
  haveI := q1_nontrivial K a b c d
  have hbij : Function.Bijective (botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) :=
    botRoute_bijective K a b c d e₄ φ₄ hφ₄ e₅ φ₅ hφ₅
  haveI : Module.Finite K (Q4 K a b c d) :=
    Module.Finite.equiv (LinearEquiv.ofBijective
      (botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅) hbij)
  have hbotMem : botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅
      ∈ quadInterSpace K a b c d (e₄ + e₅) :=
    botRoute_mem K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ ht4 ht5
  have hbotNe : botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ ≠ 0 :=
    botRoute_ne_zero_of_bijective K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅ hbij
  have hbotMemG :
      botRoute K a b c d e₄ φ₄.toLinearMap hφ₄ e₅ φ₅.toLinearMap hφ₅
        ∈ gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d) (Q4.grading K a b c d)
            (e₄ + e₅) :=
    (mem_quadInterSpace_iff_gradedHomF K a b c d).mp hbotMem
  have hle := gradedHomF_finrank_sum_le_one
    (ℳ := Q1.grading K a b c d) (𝒯 := quadEnvGrading K a b c d) (𝒩 := Q4.grading K a b c d)
    (quadEnvSplit K a b c d) (quadEnvSize_ne_zero K a b c d)
    (finrank_Q1_eq_quadEnvSize K a b c d)
    (finrank_Q4_eq_quadEnvSize K a b c d φ₄.toLinearMap hφ₄ φ₅.toLinearMap hφ₅ hbij)
  have hd :
      gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d) (Q4.grading K a b c d)
          (e₄ + e₅) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨_, hbotMemG, hbotNe⟩
  obtain ⟨-, -, hspan⟩ := parityConcentration
    (Q1.grading K a b c d) (quadEnvGrading K a b c d) (𝒩 := Q4.grading K a b c d) hle hd
  intro f hf
  have hfmemG : f ∈ gradedHomF (Q1.grading K a b c d) (quadEnvGrading K a b c d)
      (Q4.grading K a b c d) (e₄ + e₅) := (mem_quadInterSpace_iff_gradedHomF K a b c d).mp hf
  exact hspan f hfmemG _ hbotMemG hbotNe

/-! ### `chiTower` -/

section ChiTower

variable {e₁ : ZMod 2} (φ₁ : BL K a b c ≃ₗ[K] BR K a b c)
variable (ht1 : φ₁.toLinearMap ∈ interSpace K a b c e₁)
variable (e₂ : ZMod 2) (φ₂ : Q2rInner K a b c d ≃ₗ[K] Q3Inner K a b c d)
variable (hφ₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i → ∀ n : Q2rInner K a b c d,
    φ₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • φ₂ n))
variable (ht2A : ∀ ⦃k : ZMod 2⦄ ⦃x : (stdTower (K := K) a).carrier⦄,
  x ∈ (stdTower (K := K) a).grading k →
  ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
    φ₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) (x • v) w)
      = ((sgn (e₂ * k) : ℤˣ) : ℤ) •
          (x • φ₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
variable (ht2D : ∀ ⦃m : ZMod 2⦄ ⦃τ : (stdTower (K := K) d).carrier⦄,
  τ ∈ (stdTower (K := K) d).grading m →
  ∀ x : Q2rInner K a b c d,
    φ₂ (τ • x) = ((sgn (e₂ * m) : ℤˣ) : ℤ) • (τ • φ₂ x))
variable (ht2R : ∀ (τ : (stdTower (K := K) (a + b + c + d)).carrier)
  (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
  φ₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
        (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v
        (MulOpposite.op τ • w))
    = MulOpposite.op ((stdTowerCast (K := K) (by ring : a + b + c + d = a + (b + c + d))).toAlgEquiv τ)
        • φ₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
        (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))
variable (ht₂deg : ∀ jj : ZMod 2,
  ∀ n ∈ relGrading (stdTower (K := K) (a + b + c)).carrier
      (TowerColumn.grading K a (b + c)) (TowerColumn.grading K (a + b + c) d) jj,
    φ₂ n ∈ Q3Inner.grading K a b c d (jj + e₂))
variable {e₃ : ZMod 2} (φ₃ : BL K b c d ≃ₗ[K] BR K b c d)
variable (ht3 : φ₃.toLinearMap ∈ interSpace K b c d e₃)
variable {e₄ : ZMod 2} (φ₄ : BL K (a + b) c d ≃ₗ[K] BR K (a + b) c d)
variable (ht4 : φ₄.toLinearMap ∈ interSpace K (a + b) c d e₄)
variable {e₅ : ZMod 2} (φ₅ : BL K a b (c + d) ≃ₗ[K] BR K a b (c + d))
variable (ht5 : φ₅.toLinearMap ∈ interSpace K a b (c + d) e₅)
variable (he : e₁ + e₂ + e₃ = e₄ + e₅)

include ht1 in
/-- The right-recast equivariance of `φ₁`, bridged from `ht1`'s
`rightSemilinear` conjunct via `rightSemilinear_iff_recast_equivariant`
(`Iff.rfl`). -/
private theorem chiTower_hφ₁ :
    ∀ (τ : (stdTower (K := K) (a + b + c)).carrier) (m : BL K a b c),
      φ₁ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₁ m :=
  (rightSemilinear_iff_recast_equivariant K a b c).mp
    ((mem_interSpace_iff K a b c).mp ht1).2.2.2.2

include ht3 in
/-- The right-recast equivariance of `φ₃`. -/
private theorem chiTower_hφ₃ :
    ∀ (τ : (stdTower (K := K) (b + c + d)).carrier) (m : BL K b c d),
      φ₃ (MulOpposite.op τ • m) = MulOpposite.op τ • φ₃ m :=
  (rightSemilinear_iff_recast_equivariant K b c d).mp
    ((mem_interSpace_iff K b c d).mp ht3).2.2.2.2

include ht4 in
/-- The signed `(a+b)`-slot equivariance of `φ₄`, from `ht4`'s second
`interSpace` conjunct. -/
private theorem chiTower_hφ₄ :
    ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
      x ∈ (stdTower (K := K) (a + b)).grading i → ∀ n : BL K (a + b) c d,
        φ₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • φ₄ n) :=
  (mem_superEquivariant (stdTower (K := K) (a + b)).grading).mp
    ((mem_interSpace_iff K (a + b) c d).mp ht4).2.1

include ht5 in
/-- The signed `(c+d)`-slot equivariance of `φ₅`, from `ht5`'s fourth
`interSpace` conjunct. -/
private theorem chiTower_hφ₅ :
    ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
      z ∈ (stdTower (K := K) (c + d)).grading i → ∀ n : BL K a b (c + d),
        φ₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • φ₅ n) :=
  (mem_superEquivariant (stdTower (K := K) (c + d)).grading).mp
    ((mem_interSpace_iff K a b (c + d)).mp ht5).2.2.2.1

include ht1 ht2A ht2D ht2R ht₂deg ht3 he in
/-- `topRoute`'s membership, at the common degree `e₄ + e₅` (via `he`). -/
private theorem chiTower_htop :
    topRoute K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap hφ₂
        φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
      ∈ quadInterSpace K a b c d (e₄ + e₅) :=
  he ▸ topRoute_mem K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap
    hφ₂ φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3) ht1 ht2A ht2D ht2R ht₂deg ht3

include ht4 ht5 in
/-- The spanning hypothesis, at the common degree `e₄ + e₅`
(`hspanTower`). -/
private theorem chiTower_hspan :
    ∀ f ∈ quadInterSpace K a b c d (e₄ + e₅),
      ∃ cc : K, f = cc • botRoute K a b c d e₄ φ₄.toLinearMap (chiTower_hφ₄ K a b c d φ₄ ht4)
        e₅ φ₅.toLinearMap (chiTower_hφ₅ K a b c d φ₅ ht5) :=
  hspanTower K a b c d φ₄ ht4 φ₅ ht5

include ht1 ht2A ht2D ht2R ht₂deg ht3 ht4 ht5 he in
/-- **`chiTower`**: the pentagon scalar of the standard ℤ/8 tower
model, for a quadruple `(a, b, c, d)` and invertible triple-intertwiner
data at every one of the five edges (`φ₁`–`φ₅`, bundled with their
`interSpace` membership except `φ₂`, whose four extra conditions are
taken raw — `Q2rInner`/`Q3Inner` carry no `interSpace` bundle), given a
common-degree hypothesis `he : e₁ + e₂ + e₃ = e₄ + e₅`.  This is the
paper's `χ` for the standard tower model over any field with `2`
invertible, with **no one-dimensionality assumption** — it is a
*theorem*, assembled from `chiAbs` (`ChiAbs.lean`) via the dimension
arithmetic (`finrank_Q1_eq_quadEnvSize`/`finrank_Q4_eq_quadEnvSize`) and
the discharge (`hspanTower`).  The identification with the concrete
`pentagonChi` and the canonicity of the `t`'s is M8a-9. -/
noncomputable def chiTower : K :=
  chiAbs K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap hφ₂
    φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
    e₄ φ₄.toLinearMap (chiTower_hφ₄ K a b c d φ₄ ht4)
    e₅ φ₅.toLinearMap (chiTower_hφ₅ K a b c d φ₅ ht5)
    (chiTower_htop K a b c d φ₁ ht1 e₂ φ₂ hφ₂ ht2A ht2D ht2R ht₂deg φ₃ ht3 he)
    (chiTower_hspan K a b c d φ₄ ht4 φ₅ ht5)

include ht1 ht2A ht2D ht2R ht₂deg ht3 ht4 ht5 he in
/-- **`chiTower_spec`**: the defining pentagon equation `topRoute =
chiTower • botRoute`. -/
theorem chiTower_spec :
    topRoute K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap hφ₂
        φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
      = chiTower K a b c d φ₁ ht1 e₂ φ₂ hφ₂ ht2A ht2D ht2R ht₂deg φ₃ ht3 φ₄ ht4 φ₅ ht5 he
          • botRoute K a b c d e₄ φ₄.toLinearMap (chiTower_hφ₄ K a b c d φ₄ ht4)
              e₅ φ₅.toLinearMap (chiTower_hφ₅ K a b c d φ₅ ht5) :=
  chiAbs_spec K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap hφ₂
    φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
    e₄ φ₄.toLinearMap (chiTower_hφ₄ K a b c d φ₄ ht4)
    e₅ φ₅.toLinearMap (chiTower_hφ₅ K a b c d φ₅ ht5)
    (chiTower_htop K a b c d φ₁ ht1 e₂ φ₂ hφ₂ ht2A ht2D ht2R ht₂deg φ₃ ht3 he)
    (chiTower_hspan K a b c d φ₄ ht4 φ₅ ht5)

include ht1 ht2A ht2D ht2R ht₂deg ht3 ht4 ht5 he in
/-- **`chiTower_ne_zero`**: `chiTower ≠ 0`, from `topRoute`'s
bijectivity (`topRoute_bijective`, `Nontrivial Q1` from
`finrank K Q1 = quadEnvSize ≠ 0`). -/
theorem chiTower_ne_zero :
    chiTower K a b c d φ₁ ht1 e₂ φ₂ hφ₂ ht2A ht2D ht2R ht₂deg φ₃ ht3 φ₄ ht4 φ₅ ht5 he ≠ 0 := by
  haveI := q1_nontrivial K a b c d
  refine chiAbs_ne_zero K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂.toLinearMap
    hφ₂ φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
    e₄ φ₄.toLinearMap (chiTower_hφ₄ K a b c d φ₄ ht4)
    e₅ φ₅.toLinearMap (chiTower_hφ₅ K a b c d φ₅ ht5)
    (chiTower_htop K a b c d φ₁ ht1 e₂ φ₂ hφ₂ ht2A ht2D ht2R ht₂deg φ₃ ht3 he)
    (chiTower_hspan K a b c d φ₄ ht4 φ₅ ht5) ?_
  exact topRoute_ne_zero_of_bijective K a b c d φ₁.toLinearMap (chiTower_hφ₁ K a b c φ₁ ht1) e₂
    φ₂.toLinearMap hφ₂ φ₃.toLinearMap (chiTower_hφ₃ K b c d φ₃ ht3)
    (topRoute_bijective K a b c d φ₁ (chiTower_hφ₁ K a b c φ₁ ht1) e₂ φ₂ hφ₂ φ₃
      (chiTower_hφ₃ K b c d φ₃ ht3))

end ChiTower

end PentagonB

end Bimod

end Superfusion
