/-
Superfusion / Bimod / QuadMembership

Milestone M8a-8c′-2c-ii (roadmap v3): **membership of the two route
composites in the quadruple intertwiner space**.  `QuadInterSpace.lean`
constructed `quadInterSpace K a b c d e` and the two route composites
`topRoute`, `botRoute`, deferring their membership on a precisely
identified obstruction: every edge from `E2` onward folds its own
associator into its generator formula, so the transport laws of
`EdgeEquiv2.lean`–`EdgeEquivClose.lean` are established only in the
"generator-∀" style (for a spelled generator with specific internal
factors homogeneous), never for an arbitrary element of the vertex —
while `HomGrading.lean`'s `superEquivariant`/`rightSemilinear` quantify
over *all* elements.

This file resolves the obstruction along the orchestrator's design:

* (A) the `E2` `d`-slot transport, rephrased against `Q2rInner`'s own
  *signed* `d`-slot action (`EdgeEquiv2.lean`'s `comp_dslot'`), is
  *component-independent* (only `(e, |τ|)`-dependent) — the residual
  sign of the original `comp_dslot` dissolves exactly;
* (B) once every edge's conclusion sign is component-independent, the
  generator-level laws upgrade to fully universal transport laws by
  **linearity + a general Decomposition-induction helper**
  (`RelTensor.induction_on_left_homog` below): both sides of a
  transport identity are `K`-linear in the vertex element, so it
  suffices to check it on a spanning set of "first-factor-homogeneous"
  generators — reusable *verbatim* at every vertex, since every vertex
  in the pentagon is literally a `RelTensor` with a `Decomposition`
  instance on its first factor (each vertex gets its own thin
  `<Vertex>.induction_on*` bridge through its synonym `mk`, to keep the
  `RelTensor` unfolding from leaking into a nested induction's motive —
  the same discipline as the edge files' generator lemmas).  Composing
  the now-universal edge laws for `E1`–`E3` (`topRoute`) resp. `E4`,
  `E5`, `q4Close` (`botRoute`) is then direct function composition — no
  further induction needed.

**Scope landed**: for both routes, all *five* `K`-linear conditions —
the four slot super-equivariances (`topRoute_comp_aslot/bslot/cslot/
dslot`, `botRoute_comp_aslot/bslot/cslot/dslot`) and right-semilinearity
(`topRoute_comp_right`, `botRoute_comp_right`) — universal in the
vertex argument, with composite degrees `e_top = e₁ + e₂ + e₃` and
`e_bot = e₄ + e₅`.  **Deferred**: the sixth condition, `homGrading`
(`f (ℳ i) ⊆ 𝒩 (i + d)`) — its own general layer needs a *degree-
matching* induction (decomposing a homogeneous-of-total-degree-`i`
vertex element into generators whose *individual* factor degrees sum
to `i`, mirroring `tensorGrading_induction`/`GradedModule.lean`
descended through `relGrading`'s quotient, recursively at each nested
vertex level) rather than the "any degree" induction used here, and is
out of scope for this pass; assembling the final `∈ quadInterSpace`
membership statements (`mem_quadInterSpace_iff`) is deferred with it.
-/
import Superfusion.Bimod.QuadInterSpace
import Superfusion.Bimod.EdgeEquiv
import Superfusion.Bimod.EdgeEquiv2
import Superfusion.Bimod.EdgeEquiv3
import Superfusion.Bimod.EdgeEquiv4

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### General layer: homogeneous-generator induction for `RelTensor`

The one reusable induction principle behind every "generator-∀ →
universal" upgrade in this file: an arbitrary element of a balanced
tensor product `M ⊗[A] N` is a finite sum of generators `mk m n` with
`m` homogeneous (of varying degree per summand) — obtained by
composing the raw `RelTensor.induction_on` (M8a-2) with the standard
graded-module induction `DirectSum.Decomposition.inductionOn` (mathlib)
on the first factor. -/

section GeneralLayer

variable {A : Type*} [Ring A]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]

omit [Invertible (2 : K)] in
/-- **Homogeneous-generator induction**: to prove a motive for every
element of `M ⊗[A] N`, it suffices to check it on `0`, on sums, and on
generators `mk m n` with `m` homogeneous of *some* degree `j` (`n`
arbitrary). -/
@[elab_as_elim]
theorem RelTensor.induction_on_left_homog
    {motive : M ⊗[A;K] N → Prop} (z : M ⊗[A;K] N)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (m : M) (n : N), m ∈ ℳ j →
      motive (RelTensor.mk K A M N m n))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z := by
  induction z using RelTensor.induction_on with
  | zero => exact zero
  | mk m n =>
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero =>
          rw [show RelTensor.mk K A M N (0 : M) n = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | add m m' hm hm' =>
          rw [show RelTensor.mk K A M N (m + m') n
              = RelTensor.mk K A M N m n + RelTensor.mk K A M N m' n from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hm hm'
      | homogeneous xm =>
          exact homog _ xm.1 n xm.2
  | add x y hx hy => exact add x y hx hy

end GeneralLayer

/-! ### Vertex layer: two-level generator induction at `Q2`

`Q2`'s elements are, up to the motive being additive, generators
`Q2.mk (BR.mk u v) w` with `u` (the `TowerColumn K b c` factor of the
`B_R`-factor) homogeneous of some degree — obtained by composing the
general helper twice: once (unconditionally) at `Q2`'s own level, once
(gradedly) at `B_R`'s own level.  `BR.induction_on_left_homog` restates
the general helper through the synonym-valued `BR.mk` (the track's
discipline) so the nested `induction … using` call stays inside the
`B_R` alias, never leaking the raw `RelTensor` unfolding into the
outer motive. -/

/-- Raw (unconditional) generator induction at `B_R`, through its own
`mk`. -/
@[elab_as_elim]
theorem BR.induction_on {motive : BR K a b c → Prop}
    (y : BR K a b c)
    (zero : motive 0)
    (mk : ∀ (u : TowerColumn K b c) (v : TowerColumn K a (b + c)),
      motive (BR.mk K a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  RelTensor.induction_on K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (TowerColumn K a (b + c)) y zero mk add

/-- Homogeneous-generator induction at `B_R`, through its own `mk`. -/
@[elab_as_elim]
theorem BR.induction_on_left_homog {motive : BR K a b c → Prop}
    (y : BR K a b c)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : TowerColumn K b c) (v : TowerColumn K a (b + c)),
      u ∈ TowerColumn.grading K b c j → motive (BR.mk K a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K b c) y zero homog add

/-- Raw (unconditional) generator induction at `Q2`, through its own
`mk` (the track's discipline — bridges `RelTensor.induction_on`'s raw
spelling to `Q2.mk`, avoiding the `Q2`/`RelTensor` synonym boundary
leaking into a nested induction's motive). -/
@[elab_as_elim]
theorem Q2.induction_on {motive : Q2 K a b c d → Prop}
    (z : Q2 K a b c d)
    (zero : motive 0)
    (mk : ∀ (m : BR K a b c) (w : TowerColumn K (a + b + c) d),
      motive (Q2.mk K a b c d m w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (stdTower (K := K) (a + b + c)).carrier
    (BR K a b c) (TowerColumn K (a + b + c) d) z zero mk add

/-- **Two-level generator induction at `Q2`**: to prove an additive
motive for every element of `Q2`, it suffices to check it on
generators `Q2.mk (BR.mk u v) w` with `u` homogeneous. -/
@[elab_as_elim]
theorem Q2.induction_on_gen {motive : Q2 K a b c d → Prop}
    (n : Q2 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : TowerColumn K b c) (v : TowerColumn K a (b + c))
      (w : TowerColumn K (a + b + c) d), u ∈ TowerColumn.grading K b c j →
      motive (Q2.mk K a b c d (BR.mk K a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q2.induction_on K a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using BR.induction_on_left_homog K a b c with
      | zero =>
          rw [show Q2.mk K a b c d (0 : BR K a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog j u v hu => exact homog u v w hu
      | add y y' hy hy' =>
          rw [show Q2.mk K a b c d (y + y') w
              = Q2.mk K a b c d y w + Q2.mk K a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### Vertex layer: three-level generator induction at `Q2` (both
`u`, `v` homogeneous — for the `d`-slot, whose clean form still keys
its own equivariance hypothesis at the level of `Q2rInner`, needing
`v` homogeneous too). -/

/-- Homogeneous-generator induction at `B_R`, both factors, through its
own `mk`. -/
@[elab_as_elim]
theorem BR.induction_on_gen2 {motive : BR K a b c → Prop}
    (y : BR K a b c)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K b c) (v : TowerColumn K a (b + c)),
      u ∈ TowerColumn.grading K b c j → v ∈ TowerColumn.grading K a (b + c) jv →
      motive (BR.mk K a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y := by
  induction y using BR.induction_on_left_homog K a b c with
  | zero => exact zero
  | homog j u n hu =>
      induction n using DirectSum.Decomposition.inductionOn
        (TowerColumn.grading K a (b + c)) with
      | zero =>
          rw [show BR.mk K a b c u (0 : TowerColumn K a (b + c)) = 0 from by
            simp only [map_zero]]
          exact zero
      | add v v' hv hv' =>
          rw [show BR.mk K a b c u (v + v') = BR.mk K a b c u v + BR.mk K a b c u v' from by
            simp only [map_add]]
          exact add _ _ hv hv'
      | homogeneous xv => exact homog u xv.1 hu xv.2
  | add y y' hy hy' => exact add y y' hy hy'

/-- **Three-level generator induction at `Q2`**: to prove an additive
motive for every element of `Q2`, it suffices to check it on
generators `Q2.mk (BR.mk u v) w` with both `u`, `v` homogeneous. -/
@[elab_as_elim]
theorem Q2.induction_on_gen2 {motive : Q2 K a b c d → Prop}
    (n : Q2 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K b c) (v : TowerColumn K a (b + c))
      (w : TowerColumn K (a + b + c) d), u ∈ TowerColumn.grading K b c j →
      v ∈ TowerColumn.grading K a (b + c) jv →
      motive (Q2.mk K a b c d (BR.mk K a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q2.induction_on K a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using BR.induction_on_gen2 K a b c with
      | zero =>
          rw [show Q2.mk K a b c d (0 : BR K a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog u v hu hv => exact homog u v w hu hv
      | add y y' hy hy' =>
          rw [show Q2.mk K a b c d (y + y') w
              = Q2.mk K a b c d y w + Q2.mk K a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### `E2`'s slot and right transports, upgraded to universal -/

namespace E2

variable (e : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i →
  ∀ n : Q2rInner K a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- **`E2`'s `a`-slot transport, universal**: the generator-restricted
`comp_aslot` upgrades to hold for *every* `n : Q2`, by two-level
homogeneous-generator induction (`Q2.induction_on_gen`) — the sign `s`
is already component-independent (only depends on `t₂`'s own
equivariance scalar, never on the generator's degrees), so the
identity, being `K`-linear in `n`, transports along the induction's
`zero`/`add` steps unchanged. -/
theorem comp_aslot_univ {s : ℤ} {k : ZMod 2}
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht₂A : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) (x • v) w)
        = s • (x • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
    (n : Q2 K a b c d) :
    E2 K a b c d e t₂ ht₂ (x • n) = s • (x • E2 K a b c d e t₂ ht₂ n) := by
  induction n using Q2.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_aslot K a b c d e t₂ ht₂ hx ht₂A hu v w
  | add p q hp hq =>
      have h1 : E2 K a b c d e t₂ ht₂ (x • (p + q))
          = E2 K a b c d e t₂ ht₂ (x • p) + E2 K a b c d e t₂ ht₂ (x • q) := by
        rw [smul_add, map_add]
      have h2 : E2 K a b c d e t₂ ht₂ (p + q)
          = E2 K a b c d e t₂ ht₂ p + E2 K a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E2`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {i : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i)
    (n : Q2 K a b c d) :
    E2 K a b c d e t₂ ht₂ (y • n)
      = ((sgn (e * i) : ℤˣ) : ℤ) • (y • E2 K a b c d e t₂ ht₂ n) := by
  induction n using Q2.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_bslot K a b c d e t₂ ht₂ hy hu v w
  | add p q hp hq =>
      have h1 : E2 K a b c d e t₂ ht₂ (y • (p + q))
          = E2 K a b c d e t₂ ht₂ (y • p) + E2 K a b c d e t₂ ht₂ (y • q) := by
        rw [smul_add, map_add]
      have h2 : E2 K a b c d e t₂ ht₂ (p + q)
          = E2 K a b c d e t₂ ht₂ p + E2 K a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E2`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {i : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading i)
    (n : Q2 K a b c d) :
    E2 K a b c d e t₂ ht₂ (z0 • n)
      = ((sgn (e * i) : ℤˣ) : ℤ) • (z0 • E2 K a b c d e t₂ ht₂ n) := by
  induction n using Q2.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_cslot K a b c d e t₂ ht₂ hz0 hu v w
  | add p q hp hq =>
      have h1 : E2 K a b c d e t₂ ht₂ (z0 • (p + q))
          = E2 K a b c d e t₂ ht₂ (z0 • p) + E2 K a b c d e t₂ ht₂ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : E2 K a b c d e t₂ ht₂ (p + q)
          = E2 K a b c d e t₂ ht₂ p + E2 K a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast of the total coefficient algebra used by
`comp_right_univ` (matches `EdgeEquiv2.lean`'s `right_recast_eq`). -/
private theorem right_recast_eq' :
    a + b + c + d = a + (b + c + d) := by ring

/-- **`E2`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht₂R : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq' a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))
    (n : Q2 K a b c d) :
    E2 K a b c d e t₂ ht₂ (MulOpposite.op τ • n)
      = MulOpposite.op ((stdTowerCast (K := K) (right_recast_eq' a b c d)).toAlgEquiv τ)
          • E2 K a b c d e t₂ ht₂ n := by
  induction n using Q2.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_right K a b c d e t₂ ht₂ τ ht₂R hu v w
  | add p q hp hq =>
      have h1 : E2 K a b c d e t₂ ht₂ (MulOpposite.op τ • (p + q))
          = E2 K a b c d e t₂ ht₂ (MulOpposite.op τ • p)
            + E2 K a b c d e t₂ ht₂ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : E2 K a b c d e t₂ ht₂ (p + q)
          = E2 K a b c d e t₂ ht₂ p + E2 K a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`E2`'s `d`-slot transport, universal.**  Built on the *clean-form*
`comp_dslot'` (part (A)) — the sign has already dissolved, so the
upgrade is the same shape as the `a`-, `b`-, `c`-slots and `right`
transports (three-level induction, since the clean hypothesis `ht₂D'`
is phrased against `Q2rInner`'s own signed action, which the original
`comp_dslot'` derivation keys to *both* `u`'s and `v`'s degrees). -/
theorem comp_dslot_univ {s' : ℤ} {m : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₂D' : ∀ x : Q2rInner K a b c d, t₂ (τ • x) = s' • (τ • t₂ x))
    (n : Q2 K a b c d) :
    E2 K a b c d e t₂ ht₂ (τ • n) = s' • (τ • E2 K a b c d e t₂ ht₂ n) := by
  induction n using Q2.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot' K a b c d e t₂ ht₂ hτ ht₂D' hu hv w
  | add p q hp hq =>
      have h1 : E2 K a b c d e t₂ ht₂ (τ • (p + q))
          = E2 K a b c d e t₂ ht₂ (τ • p) + E2 K a b c d e t₂ ht₂ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : E2 K a b c d e t₂ ht₂ (p + q)
          = E2 K a b c d e t₂ ht₂ p + E2 K a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

end E2

/-! ### Vertex layer: generator induction at `Q3`

`Q3 = C_{b,c} ⊗_{T_{b+c}} Q3Inner` with `Q3Inner` literally
`B_R(a,b{+}c,d)` — a raw (ungraded) wrapper for `Q3` and for
`Q3Inner` (through `BR.mk`), plus a homogeneous one for each, mirroring
`Q2`'s vertex layer. -/

/-- Raw (unconditional) generator induction at `Q3Inner`, through its
own spelling `BR.mk K a (b+c) d`. -/
@[elab_as_elim]
theorem Q3Inner.induction_on {motive : Q3Inner K a b c d → Prop}
    (x : Q3Inner K a b c d)
    (zero : motive 0)
    (mk : ∀ (v : TowerColumn K (b + c) d) (w : TowerColumn K a ((b + c) + d)),
      motive (BR.mk K a (b + c) d v w : Q3Inner K a b c d))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  RelTensor.induction_on K (stdTower (K := K) ((b + c) + d)).carrier
    (TowerColumn K (b + c) d) (TowerColumn K a ((b + c) + d)) x zero mk add

/-- Homogeneous-generator induction at `Q3Inner`, through its own
spelling `BR.mk K a (b+c) d` (`v` homogeneous). -/
@[elab_as_elim]
theorem Q3Inner.induction_on_left_homog {motive : Q3Inner K a b c d → Prop}
    (x : Q3Inner K a b c d)
    (zero : motive 0)
    (homog : ∀ (i : ZMod 2) (v : TowerColumn K (b + c) d)
      (w : TowerColumn K a ((b + c) + d)),
      v ∈ TowerColumn.grading K (b + c) d i →
      motive (BR.mk K a (b + c) d v w : Q3Inner K a b c d))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K (b + c) d) x zero homog add

/-- Raw (unconditional) generator induction at `Q3`, through its own
`mk`. -/
@[elab_as_elim]
theorem Q3.induction_on {motive : Q3 K a b c d → Prop}
    (z : Q3 K a b c d)
    (zero : motive 0)
    (mk : ∀ (u : TowerColumn K b c) (x : Q3Inner K a b c d),
      motive (Q3.mk K a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (stdTower (K := K) (b + c)).carrier
    (TowerColumn K b c) (Q3Inner K a b c d) z zero mk add

/-- Homogeneous-generator induction at `Q3`, through its own `mk`
(`u` homogeneous, `Q3Inner`-component arbitrary) — the bridge avoiding
the `Q3`/`RelTensor` synonym boundary leaking into a nested
induction's motive. -/
@[elab_as_elim]
theorem Q3.induction_on_left_homog {motive : Q3 K a b c d → Prop}
    (z : Q3 K a b c d)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : TowerColumn K b c) (x : Q3Inner K a b c d),
      u ∈ TowerColumn.grading K b c j → motive (Q3.mk K a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K b c) z zero homog add

/-- **Two-level generator induction at `Q3`, raw in `Q3Inner`**: to
prove an additive motive for every element of `Q3`, it suffices to
check it on generators `Q3.mk u (BR.mk v w)` (`u`, `v`, `w`
unconstrained) — the "raw" companion of `Q3.induction_on_gen`, for the
`b`-, `c`-slots and the right action of `E3`, none of which need any
homogeneity at all. -/
@[elab_as_elim]
theorem Q3.induction_on_raw {motive : Q3 K a b c d → Prop}
    (n : Q3 K a b c d)
    (zero : motive 0)
    (mk : ∀ (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
      (w : TowerColumn K a ((b + c) + d)),
      motive (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q3.induction_on K a b c d with
  | zero => exact zero
  | mk u x =>
      induction x using Q3Inner.induction_on K a b c d with
      | zero =>
          rw [show Q3.mk K a b c d u (0 : Q3Inner K a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk v w => exact mk u v w
      | add x x' hx hx' =>
          rw [show Q3.mk K a b c d u (x + x')
              = Q3.mk K a b c d u x + Q3.mk K a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Two-level generator induction at `Q3`, `u` homogeneous**: to
prove an additive motive for every element of `Q3`, it suffices to
check it on generators `Q3.mk u (BR.mk v w)` with `u` homogeneous —
for `E3`'s `d`-slot. -/
@[elab_as_elim]
theorem Q3.induction_on_gen {motive : Q3 K a b c d → Prop}
    (n : Q3 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
      (w : TowerColumn K a ((b + c) + d)), u ∈ TowerColumn.grading K b c j →
      motive (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q3.induction_on_left_homog K a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using Q3Inner.induction_on K a b c d with
      | zero =>
          rw [show Q3.mk K a b c d u (0 : Q3Inner K a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk v w => exact homog u v w hu
      | add x x' hx hx' =>
          rw [show Q3.mk K a b c d u (x + x')
              = Q3.mk K a b c d u x + Q3.mk K a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `Q3`, `u`, `v` both
homogeneous**: for `E3`'s `a`-slot. -/
@[elab_as_elim]
theorem Q3.induction_on_gen2 {motive : Q3 K a b c d → Prop}
    (n : Q3 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
      (w : TowerColumn K a ((b + c) + d)), u ∈ TowerColumn.grading K b c j →
      v ∈ TowerColumn.grading K (b + c) d jv →
      motive (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q3.induction_on_left_homog K a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using Q3Inner.induction_on_left_homog K a b c d with
      | zero =>
          rw [show Q3.mk K a b c d u (0 : Q3Inner K a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog jv v w hv => exact homog u v w hu hv
      | add x x' hx hx' =>
          rw [show Q3.mk K a b c d u (x + x')
              = Q3.mk K a b c d u x + Q3.mk K a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `E3`'s slot and right transports, upgraded to universal -/

namespace E3

variable (t₃ : BL K b c d →ₗ[K] BR K b c d)
variable (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
  (m : BL K b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- **`E3`'s `b`-slot transport, universal** — no homogeneity needed at
all (`comp_bslot` is already unconditional in `u`, `v`, `w`), so the
upgrade is a *raw* two-level induction (`Q3.induction_on_raw`). -/
theorem comp_bslot_univ {s : ℤ} {y : (stdTower (K := K) b).carrier}
    (ht₃B : ∀ m : BL K b c d, t₃ (y • m) = s • (y • t₃ m))
    (n : Q3 K a b c d) :
    E3 K a b c d t₃ ht₃ (y • n) = s • (y • E3 K a b c d t₃ ht₃ n) := by
  induction n using Q3.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_bslot K a b c d t₃ ht₃ ht₃B u v w
  | add p q hp hq =>
      have h1 : E3 K a b c d t₃ ht₃ (y • (p + q))
          = E3 K a b c d t₃ ht₃ (y • p) + E3 K a b c d t₃ ht₃ (y • q) := by
        rw [smul_add, map_add]
      have h2 : E3 K a b c d t₃ ht₃ (p + q)
          = E3 K a b c d t₃ ht₃ p + E3 K a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E3`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {s : ℤ} {z0 : (stdTower (K := K) c).carrier}
    (ht₃C : ∀ m : BL K b c d, t₃ (z0 • m) = s • (z0 • t₃ m))
    (n : Q3 K a b c d) :
    E3 K a b c d t₃ ht₃ (z0 • n) = s • (z0 • E3 K a b c d t₃ ht₃ n) := by
  induction n using Q3.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_cslot K a b c d t₃ ht₃ ht₃C u v w
  | add p q hp hq =>
      have h1 : E3 K a b c d t₃ ht₃ (z0 • (p + q))
          = E3 K a b c d t₃ ht₃ (z0 • p) + E3 K a b c d t₃ ht₃ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : E3 K a b c d t₃ ht₃ (p + q)
          = E3 K a b c d t₃ ht₃ p + E3 K a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E3`'s right-action transport, universal** — no cast (`Q3`'s and
`Q4`'s right-coefficient towers coincide syntactically), no
homogeneity. -/
theorem comp_right_univ (τ : ((stdTower (K := K) (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (n : Q3 K a b c d) :
    E3 K a b c d t₃ ht₃ (τ • n) = τ • E3 K a b c d t₃ ht₃ n := by
  induction n using Q3.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_right K a b c d t₃ ht₃ τ u v w
  | add p q hp hq =>
      have h1 : E3 K a b c d t₃ ht₃ (τ • (p + q))
          = E3 K a b c d t₃ ht₃ (τ • p) + E3 K a b c d t₃ ht₃ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : E3 K a b c d t₃ ht₃ (p + q)
          = E3 K a b c d t₃ ht₃ p + E3 K a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`E3`'s `d`-slot transport, universal** — `u` homogeneous
(`Q3.induction_on_gen`). -/
theorem comp_dslot_univ {s : ℤ} {m : ZMod 2}
    {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₃D : ∀ n : BL K b c d, t₃ (τ • n) = s • (τ • t₃ n))
    (n : Q3 K a b c d) :
    E3 K a b c d t₃ ht₃ (τ • n) = s • (τ • E3 K a b c d t₃ ht₃ n) := by
  induction n using Q3.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_dslot K a b c d t₃ ht₃ hτ ht₃D hu v w
  | add p q hp hq =>
      have h1 : E3 K a b c d t₃ ht₃ (τ • (p + q))
          = E3 K a b c d t₃ ht₃ (τ • p) + E3 K a b c d t₃ ht₃ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : E3 K a b c d t₃ ht₃ (p + q)
          = E3 K a b c d t₃ ht₃ p + E3 K a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E3`'s `a`-slot transport, universal** — `u`, `v` both
homogeneous (`Q3.induction_on_gen2`). -/
theorem comp_aslot_univ {e k : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e))
    {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (n : Q3 K a b c d) :
    E3 K a b c d t₃ ht₃ (x • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (x • E3 K a b c d t₃ ht₃ n) := by
  induction n using Q3.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_aslot K a b c d t₃ ht₃ ht₃deg hx hu hv w
  | add p q hp hq =>
      have h1 : E3 K a b c d t₃ ht₃ (x • (p + q))
          = E3 K a b c d t₃ ht₃ (x • p) + E3 K a b c d t₃ ht₃ (x • q) := by
        rw [smul_add, map_add]
      have h2 : E3 K a b c d t₃ ht₃ (p + q)
          = E3 K a b c d t₃ ht₃ p + E3 K a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

end E3

/-! ### `topRoute`'s slot and right transports

With `E1` already universal (`EdgeEquiv.lean`, general `RelTensor.map`
descent) and `E2`, `E3` upgraded above, `topRoute = E3 ∘ E2 ∘ E1`'s own
transport laws are now *direct function composition* — no further
induction needed.  Each condition takes, beyond `topRoute`'s own
`t₁`/`ht₁`/`e₂`/`t₂`/`ht₂`/`t₃`/`ht₃` bundle, the *further* slot
equivariances of `t₁` (of a declared degree `e₁`) and `t₃` (of a
declared degree `e₃`) that `E1.comp_*`/`E3.comp_*_univ` need, and of
`t₂` for the `a`-, `d`-slots (`E2.comp_aslot_univ`/`comp_dslot_univ`
need `t₂`'s own equivariance there, beyond its `ht₂` bundle for the
`(b+c)`-slot alone) — i.e. exactly the data of `t₁ ∈ interSpace K a b c
e₁`, `t₃ ∈ interSpace K b c d e₃`, and `t₂`'s own remaining slot
equivariances of its declared degree `e₂`.  The composite degree is
`e_top = e₁ + e₂ + e₃`. -/

section TopRoute

variable (t₁ : BL K a b c →ₗ[K] BR K a b c)
variable (ht₁ : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier)
  (m : BL K a b c), t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
variable (e₂ : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i →
  ∀ n : Q2rInner K a b c d,
    t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
variable (t₃ : BL K b c d →ₗ[K] BR K b c d)
variable (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
  (m : BL K b c d), t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

private theorem topRoute_apply (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      = E3 K a b c d t₃ ht₃
          (E2 K a b c d e₂ t₂ ht₂ (E1 K a b c d t₁ ht₁ z)) := by
  show (E3 K a b c d t₃ ht₃ ∘ₗ E2 K a b c d e₂ t₂ ht₂ ∘ₗ E1 K a b c d t₁ ht₁) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]

private theorem zmod2_topRoute_deg (e₁ e₂ e₃ k : ZMod 2) :
    e₁ * k + e₂ * k + e₃ * k = (e₁ + e₂ + e₃) * k := by ring

/-- The associativity recast used by `topRoute_comp_right` (matches
`QuadInterSpace.lean`'s `quadRightCast_eq` and `E2`'s own
`right_recast_eq`). -/
private theorem topRoute_right_recast_eq :
    a + b + c + d = a + (b + c + d) := by ring

/-- **`topRoute`'s `a`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem topRoute_comp_aslot
    {e₁ e₃ k : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht1A : ∀ m : BL K a b c, t₁ (x • m) = ((sgn (e₁ * k) : ℤˣ) : ℤ) • (x • t₁ m))
    (ht2A : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) (x • v) w)
        = ((sgn (e₂ * k) : ℤˣ) : ℤ) •
            (x • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
    (ht3deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e₃))
    (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (x • z)
      = ((sgn ((e₁ + e₂ + e₃) * k) : ℤˣ) : ℤ) •
          (x • topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [topRoute_apply, topRoute_apply,
    E1.comp_aslot K a b c d t₁ ht₁ ht1A z, map_zsmul,
    E2.comp_aslot_univ K a b c d e₂ t₂ ht₂ hx ht2A, map_zsmul, map_zsmul,
    E3.comp_aslot_univ K a b c d t₃ ht₃ ht3deg hx, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`topRoute`'s `b`-slot transport**, degree `e₁ + e₂ + e₃` — `t₂`
needs no extra hypothesis (the `b`-slot is a *spectator* for `E2`). -/
theorem topRoute_comp_bslot
    {e₁ e₃ i : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i)
    (ht1B : ∀ m : BL K a b c, t₁ (y • m) = ((sgn (e₁ * i) : ℤˣ) : ℤ) • (y • t₁ m))
    (ht3B : ∀ m : BL K b c d, t₃ (y • m) = ((sgn (e₃ * i) : ℤˣ) : ℤ) • (y • t₃ m))
    (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (y • z)
      = ((sgn ((e₁ + e₂ + e₃) * i) : ℤˣ) : ℤ) •
          (y • topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [topRoute_apply, topRoute_apply,
    E1.comp_bslot K a b c d t₁ ht₁ ht1B z, map_zsmul,
    E2.comp_bslot_univ K a b c d e₂ t₂ ht₂ hy, map_zsmul, map_zsmul,
    E3.comp_bslot_univ K a b c d t₃ ht₃ ht3B, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`topRoute`'s `c`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem topRoute_comp_cslot
    {e₁ e₃ i : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading i)
    (ht1C : ∀ m : BL K a b c, t₁ (z0 • m) = ((sgn (e₁ * i) : ℤˣ) : ℤ) • (z0 • t₁ m))
    (ht3C : ∀ m : BL K b c d, t₃ (z0 • m) = ((sgn (e₃ * i) : ℤˣ) : ℤ) • (z0 • t₃ m))
    (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (z0 • z)
      = ((sgn ((e₁ + e₂ + e₃) * i) : ℤˣ) : ℤ) •
          (z0 • topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [topRoute_apply, topRoute_apply,
    E1.comp_cslot K a b c d t₁ ht₁ ht1C z, map_zsmul,
    E2.comp_cslot_univ K a b c d e₂ t₂ ht₂ hz0, map_zsmul, map_zsmul,
    E3.comp_cslot_univ K a b c d t₃ ht₃ ht3C, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`topRoute`'s `d`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem topRoute_comp_dslot
    {e₁ e₃ m : ZMod 2} {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (hte1 : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K a b c j',
      t₁ n ∈ BR.grading K a b c (j' + e₁))
    (ht2D' : ∀ x : Q2rInner K a b c d,
      t₂ (τ • x) = ((sgn (e₂ * m) : ℤˣ) : ℤ) • (τ • t₂ x))
    (ht3D : ∀ n : BL K b c d, t₃ (τ • n) = ((sgn (e₃ * m) : ℤˣ) : ℤ) • (τ • t₃ n))
    (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (τ • z)
      = ((sgn ((e₁ + e₂ + e₃) * m) : ℤˣ) : ℤ) •
          (τ • topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [topRoute_apply, topRoute_apply,
    E1.comp_dslot K a b c d t₁ ht₁ hte1 hτ z, map_zsmul,
    E2.comp_dslot_univ K a b c d e₂ t₂ ht₂ hτ ht2D', map_zsmul, map_zsmul,
    E3.comp_dslot_univ K a b c d t₃ ht₃ hτ ht3D, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`topRoute`'s right-action transport**, along the associativity
recast `T_{((a+b)+c)+d} ≅ T_{a+((b+c)+d)}` (`quadRightCast_eq`,
`QuadInterSpace.lean`) — the *same* recast as `E2`'s own `comp_right`
(`E1`'s and `E3`'s legs carry no cast at all). -/
theorem topRoute_comp_right
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht2R : ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((stdTowerCast (K := K) (topRoute_right_recast_eq a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))
    (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (MulOpposite.op τ • z)
      = MulOpposite.op ((stdTowerCast (K := K)
            (topRoute_right_recast_eq a b c d)).toAlgEquiv τ)
          • topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z := by
  rw [topRoute_apply, topRoute_apply,
    E1.comp_right K a b c d t₁ ht₁ (MulOpposite.op τ) z,
    E2.comp_right_univ K a b c d e₂ t₂ ht₂ τ ht2R,
    E3.comp_right_univ K a b c d t₃ ht₃]

end TopRoute

/-! ### Vertex layer: generator induction at `Q1` (mirrors `Q2`,
`B_L` in place of `B_R`) -/

/-- Homogeneous-generator induction at `B_L`, through its own `mk`. -/
@[elab_as_elim]
theorem BL.induction_on_left_homog {motive : BL K a b c → Prop}
    (y : BL K a b c)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : TowerColumn K a b) (v : TowerColumn K (a + b) c),
      u ∈ TowerColumn.grading K a b j → motive (BL.mk K a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K a b) y zero homog add

/-- Homogeneous-generator induction at `B_L`, both factors. -/
@[elab_as_elim]
theorem BL.induction_on_gen2 {motive : BL K a b c → Prop}
    (y : BL K a b c)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K a b) (v : TowerColumn K (a + b) c),
      u ∈ TowerColumn.grading K a b j → v ∈ TowerColumn.grading K (a + b) c jv →
      motive (BL.mk K a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y := by
  induction y using BL.induction_on_left_homog K a b c with
  | zero => exact zero
  | homog j u n hu =>
      induction n using DirectSum.Decomposition.inductionOn
        (TowerColumn.grading K (a + b) c) with
      | zero =>
          rw [show BL.mk K a b c u (0 : TowerColumn K (a + b) c) = 0 from by
            simp only [map_zero]]
          exact zero
      | add v v' hv hv' =>
          rw [show BL.mk K a b c u (v + v') = BL.mk K a b c u v + BL.mk K a b c u v' from by
            simp only [map_add]]
          exact add _ _ hv hv'
      | homogeneous xv => exact homog u xv.1 hu xv.2
  | add y y' hy hy' => exact add y y' hy hy'

/-- Raw (unconditional) generator induction at `Q1`, through its own
`mk`. -/
@[elab_as_elim]
theorem Q1.induction_on {motive : Q1 K a b c d → Prop}
    (z : Q1 K a b c d)
    (zero : motive 0)
    (mk : ∀ (m : BL K a b c) (w : TowerColumn K (a + b + c) d),
      motive (Q1.mk K a b c d m w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (stdTower (K := K) (a + b + c)).carrier
    (BL K a b c) (TowerColumn K (a + b + c) d) z zero mk add

/-- **Two-level generator induction at `Q1`**, `u` homogeneous. -/
@[elab_as_elim]
theorem Q1.induction_on_gen {motive : Q1 K a b c d → Prop}
    (n : Q1 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : TowerColumn K a b) (v : TowerColumn K (a + b) c)
      (w : TowerColumn K (a + b + c) d), u ∈ TowerColumn.grading K a b j →
      motive (Q1.mk K a b c d (BL.mk K a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q1.induction_on K a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using BL.induction_on_left_homog K a b c with
      | zero =>
          rw [show Q1.mk K a b c d (0 : BL K a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog j u v hu => exact homog u v w hu
      | add y y' hy hy' =>
          rw [show Q1.mk K a b c d (y + y') w
              = Q1.mk K a b c d y w + Q1.mk K a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `Q1`**, `u`, `v` both
homogeneous — for `E4`'s `d`-slot. -/
@[elab_as_elim]
theorem Q1.induction_on_gen2 {motive : Q1 K a b c d → Prop}
    (n : Q1 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K a b) (v : TowerColumn K (a + b) c)
      (w : TowerColumn K (a + b + c) d), u ∈ TowerColumn.grading K a b j →
      v ∈ TowerColumn.grading K (a + b) c jv →
      motive (Q1.mk K a b c d (BL.mk K a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q1.induction_on K a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using BL.induction_on_gen2 K a b c with
      | zero =>
          rw [show Q1.mk K a b c d (0 : BL K a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog u v hu hv => exact homog u v w hu hv
      | add y y' hy hy' =>
          rw [show Q1.mk K a b c d (y + y') w
              = Q1.mk K a b c d y w + Q1.mk K a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### `E4`'s slot and right transports, upgraded to universal -/

namespace E4

variable (e : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
  x ∈ (stdTower (K := K) (a + b)).grading i →
  ∀ n : BL K (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- **`E4`'s `a`-slot transport, universal** — the *spectator* slot,
no extra hypothesis on `t₄`. -/
theorem comp_aslot_univ {k : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (n : Q1 K a b c d) :
    E4 K a b c d e t₄ ht₄ (x • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (x • E4 K a b c d e t₄ ht₄ n) := by
  induction n using Q1.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_aslot K a b c d e t₄ ht₄ hx hu v w
  | add p q hp hq =>
      have h1 : E4 K a b c d e t₄ ht₄ (x • (p + q))
          = E4 K a b c d e t₄ ht₄ (x • p) + E4 K a b c d e t₄ ht₄ (x • q) := by
        rw [smul_add, map_add]
      have h2 : E4 K a b c d e t₄ ht₄ (p + q)
          = E4 K a b c d e t₄ ht₄ p + E4 K a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E4`'s `b`-slot transport, universal** — the *spectator* slot. -/
theorem comp_bslot_univ {k : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    (n : Q1 K a b c d) :
    E4 K a b c d e t₄ ht₄ (y • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (y • E4 K a b c d e t₄ ht₄ n) := by
  induction n using Q1.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_bslot K a b c d e t₄ ht₄ hy hu v w
  | add p q hp hq =>
      have h1 : E4 K a b c d e t₄ ht₄ (y • (p + q))
          = E4 K a b c d e t₄ ht₄ (y • p) + E4 K a b c d e t₄ ht₄ (y • q) := by
        rw [smul_add, map_add]
      have h2 : E4 K a b c d e t₄ ht₄ (p + q)
          = E4 K a b c d e t₄ ht₄ p + E4 K a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E4`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {s : ℤ} {k : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading k)
    (ht₄C : ∀ n : BL K (a + b) c d, t₄ (z0 • n) = s • (z0 • t₄ n))
    (n : Q1 K a b c d) :
    E4 K a b c d e t₄ ht₄ (z0 • n) = s • (z0 • E4 K a b c d e t₄ ht₄ n) := by
  induction n using Q1.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_cslot K a b c d e t₄ ht₄ hz0 ht₄C hu v w
  | add p q hp hq =>
      have h1 : E4 K a b c d e t₄ ht₄ (z0 • (p + q))
          = E4 K a b c d e t₄ ht₄ (z0 • p) + E4 K a b c d e t₄ ht₄ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : E4 K a b c d e t₄ ht₄ (p + q)
          = E4 K a b c d e t₄ ht₄ p + E4 K a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E4`'s `d`-slot transport, universal.** -/
theorem comp_dslot_univ {s' : ℤ} {m : ZMod 2} {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading m)
    (ht₄D : ∀ n : BL K (a + b) c d, t₄ (τ • n) = s' • (τ • t₄ n))
    (n : Q1 K a b c d) :
    E4 K a b c d e t₄ ht₄ (τ • n) = s' • (τ • E4 K a b c d e t₄ ht₄ n) := by
  induction n using Q1.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot K a b c d e t₄ ht₄ hτ ht₄D hu hv w
  | add p q hp hq =>
      have h1 : E4 K a b c d e t₄ ht₄ (τ • (p + q))
          = E4 K a b c d e t₄ ht₄ (τ • p) + E4 K a b c d e t₄ ht₄ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : E4 K a b c d e t₄ ht₄ (p + q)
          = E4 K a b c d e t₄ ht₄ p + E4 K a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast used by `comp_right_univ` (matches
`EdgeEquiv4.lean`'s `right_recast_eq`). -/
private theorem right_recast_eq4 : a + b + c + d = a + b + (c + d) := by ring

/-- **`E4`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht₄R : ∀ n : BL K (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((stdTowerCast (K := K)
              (right_recast_eq4 a b c d)).toAlgEquiv τ) • t₄ n)
    (n : Q1 K a b c d) :
    E4 K a b c d e t₄ ht₄ (MulOpposite.op τ • n)
      = MulOpposite.op ((stdTowerCast (K := K)
            (right_recast_eq4 a b c d)).toAlgEquiv τ)
          • E4 K a b c d e t₄ ht₄ n := by
  induction n using Q1.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_right K a b c d e t₄ ht₄ τ ht₄R hu v w
  | add p q hp hq =>
      have h1 : E4 K a b c d e t₄ ht₄ (MulOpposite.op τ • (p + q))
          = E4 K a b c d e t₄ ht₄ (MulOpposite.op τ • p)
            + E4 K a b c d e t₄ ht₄ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : E4 K a b c d e t₄ ht₄ (p + q)
          = E4 K a b c d e t₄ ht₄ p + E4 K a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end E4

/-! ### Vertex layer: generator induction at `Q5`

`Q5 = C_{a,b} ⊗_{T_{a+b}} B_R(a{+}b,c,d)` — the same shape as `Q3`,
directly (no `…Inner` def-wrapping needed: `Q5`'s second factor is
literally `BR K (a+b) c d`). -/

/-- Raw (unconditional) generator induction at `Q5`, through its own
`mk`. -/
@[elab_as_elim]
theorem Q5.induction_on {motive : Q5 K a b c d → Prop}
    (z : Q5 K a b c d)
    (zero : motive 0)
    (mk : ∀ (u : TowerColumn K a b) (x : BR K (a + b) c d),
      motive (Q5.mk K a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (stdTower (K := K) (a + b)).carrier
    (TowerColumn K a b) (BR K (a + b) c d) z zero mk add

/-- Homogeneous-generator induction at `Q5`, through its own `mk`. -/
@[elab_as_elim]
theorem Q5.induction_on_left_homog {motive : Q5 K a b c d → Prop}
    (z : Q5 K a b c d)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : TowerColumn K a b) (x : BR K (a + b) c d),
      u ∈ TowerColumn.grading K a b j → motive (Q5.mk K a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K a b) z zero homog add

/-- **Three-level generator induction at `Q5`**, `u`, `v` both
homogeneous — every `E5` condition needs both. -/
@[elab_as_elim]
theorem Q5.induction_on_gen2 {motive : Q5 K a b c d → Prop}
    (n : Q5 K a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : TowerColumn K a b) (v : TowerColumn K c d)
      (w : TowerColumn K (a + b) (c + d)), u ∈ TowerColumn.grading K a b j →
      v ∈ TowerColumn.grading K c d jv →
      motive (Q5.mk K a b c d u (BR.mk K (a + b) c d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q5.induction_on_left_homog K a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using BR.induction_on_left_homog K (a + b) c d with
      | zero =>
          rw [show Q5.mk K a b c d u (0 : BR K (a + b) c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog jv v w hv => exact homog u v w hu hv
      | add x x' hx hx' =>
          rw [show Q5.mk K a b c d u (x + x')
              = Q5.mk K a b c d u x + Q5.mk K a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `E5`'s slot and right transports, upgraded to universal -/

namespace E5

variable (e : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
  z ∈ (stdTower (K := K) (c + d)).grading i →
  ∀ n : BL K a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- **`E5`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {s : ℤ} {k : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht₅A : ∀ n : BL K a b (c + d), t₅ (x • n) = s • (x • t₅ n))
    (n : Q5 K a b c d) :
    E5 K a b c d e t₅ ht₅ (x • n) = s • (x • E5 K a b c d e t₅ ht₅ n) := by
  induction n using Q5.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_aslot K a b c d e t₅ ht₅ hx ht₅A hv hu w
  | add p q hp hq =>
      have h1 : E5 K a b c d e t₅ ht₅ (x • (p + q))
          = E5 K a b c d e t₅ ht₅ (x • p) + E5 K a b c d e t₅ ht₅ (x • q) := by
        rw [smul_add, map_add]
      have h2 : E5 K a b c d e t₅ ht₅ (p + q)
          = E5 K a b c d e t₅ ht₅ p + E5 K a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E5`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {s : ℤ} {k : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    (ht₅B : ∀ n : BL K a b (c + d), t₅ (y • n) = s • (y • t₅ n))
    (n : Q5 K a b c d) :
    E5 K a b c d e t₅ ht₅ (y • n) = s • (y • E5 K a b c d e t₅ ht₅ n) := by
  induction n using Q5.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_bslot K a b c d e t₅ ht₅ hy ht₅B hv hu w
  | add p q hp hq =>
      have h1 : E5 K a b c d e t₅ ht₅ (y • (p + q))
          = E5 K a b c d e t₅ ht₅ (y • p) + E5 K a b c d e t₅ ht₅ (y • q) := by
        rw [smul_add, map_add]
      have h2 : E5 K a b c d e t₅ ht₅ (p + q)
          = E5 K a b c d e t₅ ht₅ p + E5 K a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E5`'s `c`-slot transport, universal** — the *spectator* slot,
no extra hypothesis on `t₅`. -/
theorem comp_cslot_univ {k : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading k)
    (n : Q5 K a b c d) :
    E5 K a b c d e t₅ ht₅ (z0 • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (z0 • E5 K a b c d e t₅ ht₅ n) := by
  induction n using Q5.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_cslot K a b c d e t₅ ht₅ hz0 hv hu w
  | add p q hp hq =>
      have h1 : E5 K a b c d e t₅ ht₅ (z0 • (p + q))
          = E5 K a b c d e t₅ ht₅ (z0 • p) + E5 K a b c d e t₅ ht₅ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : E5 K a b c d e t₅ ht₅ (p + q)
          = E5 K a b c d e t₅ ht₅ p + E5 K a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`E5`'s `d`-slot transport, universal** — the *spectator* slot. -/
theorem comp_dslot_univ {k : ZMod 2} {t : (stdTower (K := K) d).carrier}
    (ht : t ∈ (stdTower (K := K) d).grading k)
    (n : Q5 K a b c d) :
    E5 K a b c d e t₅ ht₅ (t • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (t • E5 K a b c d e t₅ ht₅ n) := by
  induction n using Q5.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot K a b c d e t₅ ht₅ ht hv hu w
  | add p q hp hq =>
      have h1 : E5 K a b c d e t₅ ht₅ (t • (p + q))
          = E5 K a b c d e t₅ ht₅ (t • p) + E5 K a b c d e t₅ ht₅ (t • q) := by
        rw [smul_add, map_add]
      have h2 : E5 K a b c d e t₅ ht₅ (p + q)
          = E5 K a b c d e t₅ ht₅ p + E5 K a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast used by `comp_right_univ` (matches
`EdgeEquiv5.lean`'s `right_recast_eq5`). -/
private theorem right_recast_eq5' : a + b + (c + d) = a + (b + (c + d)) := by ring

/-- **`E5`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (stdTower (K := K) (a + b + (c + d))).carrier)
    (ht₅R : ∀ n : BL K a b (c + d),
      t₅ (MulOpposite.op τ • n)
        = MulOpposite.op ((stdTowerCast (K := K)
              (right_recast_eq5' a b c d)).toAlgEquiv τ) • t₅ n)
    (n : Q5 K a b c d) :
    E5 K a b c d e t₅ ht₅ (MulOpposite.op τ • n)
      = MulOpposite.op ((stdTowerCast (K := K)
            (right_recast_eq5' a b c d)).toAlgEquiv τ)
          • E5 K a b c d e t₅ ht₅ n := by
  induction n using Q5.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_right K a b c d e t₅ ht₅ τ ht₅R hv hu w
  | add p q hp hq =>
      have h1 : E5 K a b c d e t₅ ht₅ (MulOpposite.op τ • (p + q))
          = E5 K a b c d e t₅ ht₅ (MulOpposite.op τ • p)
            + E5 K a b c d e t₅ ht₅ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : E5 K a b c d e t₅ ht₅ (p + q)
          = E5 K a b c d e t₅ ht₅ p + E5 K a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end E5

/-! ### Vertex layer: generator induction at `Q4r`

`Q4r = C_{c,d} ⊗_{T_{c+d}} B_R(a,b,c{+}d)` — the same shape as `Q3`,
`Q5`. -/

/-- Raw (unconditional) generator induction at `Q4r`, through its own
`mk`. -/
@[elab_as_elim]
theorem Q4r.induction_on {motive : Q4r K a b c d → Prop}
    (z : Q4r K a b c d)
    (zero : motive 0)
    (mk : ∀ (v : TowerColumn K c d) (x : BR K a b (c + d)),
      motive (Q4r.mk K a b c d v x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (stdTower (K := K) (c + d)).carrier
    (TowerColumn K c d) (BR K a b (c + d)) z zero mk add

/-- Homogeneous-generator induction at `Q4r`, through its own `mk`. -/
@[elab_as_elim]
theorem Q4r.induction_on_left_homog {motive : Q4r K a b c d → Prop}
    (z : Q4r K a b c d)
    (zero : motive 0)
    (homog : ∀ (i : ZMod 2) (v : TowerColumn K c d) (x : BR K a b (c + d)),
      v ∈ TowerColumn.grading K c d i → motive (Q4r.mk K a b c d v x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on_left_homog K (TowerColumn.grading K c d) z zero homog add

/-- **Two-level generator induction at `Q4r`, raw in the `B_R`
factor**: for `comp_cslot`, `comp_dslot`, `comp_right`, none of which
need any homogeneity at all. -/
@[elab_as_elim]
theorem Q4r.induction_on_raw {motive : Q4r K a b c d → Prop}
    (n : Q4r K a b c d)
    (zero : motive 0)
    (mk : ∀ (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
      (w : TowerColumn K a (b + (c + d))),
      motive (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q4r.induction_on K a b c d with
  | zero => exact zero
  | mk v x =>
      induction x using BR.induction_on K a b (c + d) with
      | zero =>
          rw [show Q4r.mk K a b c d v (0 : BR K a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk u w => exact mk v u w
      | add x x' hx hx' =>
          rw [show Q4r.mk K a b c d v (x + x')
              = Q4r.mk K a b c d v x + Q4r.mk K a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Two-level generator induction at `Q4r`, `v` homogeneous**: for
`comp_bslot`. -/
@[elab_as_elim]
theorem Q4r.induction_on_gen {motive : Q4r K a b c d → Prop}
    (n : Q4r K a b c d)
    (zero : motive 0)
    (homog : ∀ {i : ZMod 2} (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
      (w : TowerColumn K a (b + (c + d))), v ∈ TowerColumn.grading K c d i →
      motive (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q4r.induction_on_left_homog K a b c d with
  | zero => exact zero
  | homog i v x hv =>
      induction x using BR.induction_on K a b (c + d) with
      | zero =>
          rw [show Q4r.mk K a b c d v (0 : BR K a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk u w => exact homog v u w hv
      | add x x' hx hx' =>
          rw [show Q4r.mk K a b c d v (x + x')
              = Q4r.mk K a b c d v x + Q4r.mk K a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `Q4r`, `v`, `u` both
homogeneous**: for `comp_aslot`. -/
@[elab_as_elim]
theorem Q4r.induction_on_gen2 {motive : Q4r K a b c d → Prop}
    (n : Q4r K a b c d)
    (zero : motive 0)
    (homog : ∀ {i j : ZMod 2} (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
      (w : TowerColumn K a (b + (c + d))), v ∈ TowerColumn.grading K c d i →
      u ∈ TowerColumn.grading K b (c + d) j →
      motive (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using Q4r.induction_on_left_homog K a b c d with
  | zero => exact zero
  | homog i v x hv =>
      induction x using BR.induction_on_left_homog K a b (c + d) with
      | zero =>
          rw [show Q4r.mk K a b c d v (0 : BR K a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog j u w hu => exact homog v u w hv hu
      | add x x' hx hx' =>
          rw [show Q4r.mk K a b c d v (x + x')
              = Q4r.mk K a b c d v x + Q4r.mk K a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `q4Close`'s slot and right transports, upgraded to universal -/

namespace Q4Close

/-- **`q4Close`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {k : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (n : Q4r K a b c d) :
    q4Close K a b c d (x • n) = x • q4Close K a b c d n := by
  induction n using Q4r.induction_on_gen2 K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog v u w hv hu => exact comp_aslot K a b c d hv hu hx w
  | add p q hp hq =>
      have h1 : q4Close K a b c d (x • (p + q))
          = q4Close K a b c d (x • p) + q4Close K a b c d (x • q) := by
        rw [smul_add, map_add]
      have h2 : q4Close K a b c d (p + q)
          = q4Close K a b c d p + q4Close K a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`q4Close`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {i : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading i)
    (n : Q4r K a b c d) :
    q4Close K a b c d (y • n) = y • q4Close K a b c d n := by
  induction n using Q4r.induction_on_gen K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog v u w hv => exact comp_bslot K a b c d hv hy u w
  | add p q hp hq =>
      have h1 : q4Close K a b c d (y • (p + q))
          = q4Close K a b c d (y • p) + q4Close K a b c d (y • q) := by
        rw [smul_add, map_add]
      have h2 : q4Close K a b c d (p + q)
          = q4Close K a b c d p + q4Close K a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`q4Close`'s `c`-slot transport, universal** — fully direct, no
homogeneity anywhere. -/
theorem comp_cslot_univ (z0 : (stdTower (K := K) c).carrier) (n : Q4r K a b c d) :
    q4Close K a b c d (z0 • n) = z0 • q4Close K a b c d n := by
  induction n using Q4r.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_cslot K a b c d v u w z0
  | add p q hp hq =>
      have h1 : q4Close K a b c d (z0 • (p + q))
          = q4Close K a b c d (z0 • p) + q4Close K a b c d (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : q4Close K a b c d (p + q)
          = q4Close K a b c d p + q4Close K a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`q4Close`'s `d`-slot transport, universal.** -/
theorem comp_dslot_univ (t : (stdTower (K := K) d).carrier) (n : Q4r K a b c d) :
    q4Close K a b c d (t • n) = t • q4Close K a b c d n := by
  induction n using Q4r.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_dslot K a b c d v u w t
  | add p q hp hq =>
      have h1 : q4Close K a b c d (t • (p + q))
          = q4Close K a b c d (t • p) + q4Close K a b c d (t • q) := by
        rw [smul_add, map_add]
      have h2 : q4Close K a b c d (p + q)
          = q4Close K a b c d p + q4Close K a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`q4Close`'s right-action transport, universal.** -/
theorem comp_right_univ (τ : (stdTower (K := K) (a + (b + (c + d)))).carrier)
    (n : Q4r K a b c d) :
    q4Close K a b c d (MulOpposite.op τ • n)
      = MulOpposite.op ((stdTowerCast (K := K)
            (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm τ)
          • q4Close K a b c d n := by
  induction n using Q4r.induction_on_raw K a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_right K a b c d v u w τ
  | add p q hp hq =>
      have h1 : q4Close K a b c d (MulOpposite.op τ • (p + q))
          = q4Close K a b c d (MulOpposite.op τ • p)
            + q4Close K a b c d (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : q4Close K a b c d (p + q)
          = q4Close K a b c d p + q4Close K a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end Q4Close

/-! ### `botRoute`'s slot and right transports

With `E4`, `E5`, `q4Close` all upgraded above, `botRoute = q4Close ∘
E5 ∘ E4`'s own transport laws are again direct function composition.
Unlike `topRoute`, `t₄`'s and `t₅`'s degrees `e₄`, `e₅` are already
part of `botRoute`'s own argument bundle (no extra `e`'s needed); the
composite degree is `e_bot = e₄ + e₅` (`q4Close` itself is degree-`0`,
`EdgeEquivClose.lean`'s `mem_grading`). -/

section BotRoute

variable (e₄ : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
  x ∈ (stdTower (K := K) (a + b)).grading i →
  ∀ n : BL K (a + b) c d,
    t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
variable (e₅ : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
  z ∈ (stdTower (K := K) (c + d)).grading i →
  ∀ n : BL K a b (c + d),
    t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))

private theorem botRoute_apply (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      = q4Close K a b c d
          (E5 K a b c d e₅ t₅ ht₅ (E4 K a b c d e₄ t₄ ht₄ z)) := by
  show ((q4Close K a b c d).toLinearMap ∘ₗ E5 K a b c d e₅ t₅ ht₅
      ∘ₗ E4 K a b c d e₄ t₄ ht₄) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

private theorem zmod2_botRoute_deg (e₄ e₅ k : ZMod 2) :
    e₄ * k + e₅ * k = (e₄ + e₅) * k := by ring

/-- The associativity recasts used by `botRoute_comp_right` (match
`E4`'s own `right_recast_eq4` and `E5`'s own `right_recast_eq5`). -/
private theorem botRoute_right_recast_eq4 : a + b + c + d = a + b + (c + d) := by ring

private theorem botRoute_right_recast_eq5 : a + b + (c + d) = a + (b + (c + d)) := by ring

/-- **`botRoute`'s `a`-slot transport**, degree `e₄ + e₅` — `E4`'s leg
is a *spectator* (`sgn (e₄ k)`, no extra hypothesis on `t₄`), `E5`'s
needs `t₅`'s own `a`-slot equivariance (declared of `t₅`'s degree
`e₅`), `q4Close`'s is unconditional. -/
theorem botRoute_comp_aslot
    {k : ZMod 2} {x : (stdTower (K := K) a).carrier}
    (hx : x ∈ (stdTower (K := K) a).grading k)
    (ht5A : ∀ n : BL K a b (c + d), t₅ (x • n) = ((sgn (e₅ * k) : ℤˣ) : ℤ) • (x • t₅ n))
    (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (x • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (x • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [botRoute_apply, botRoute_apply,
    E4.comp_aslot_univ K a b c d e₄ t₄ ht₄ hx, map_zsmul,
    E5.comp_aslot_univ K a b c d e₅ t₅ ht₅ hx ht5A, map_zsmul, map_zsmul,
    Q4Close.comp_aslot_univ K a b c d hx, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`botRoute`'s `b`-slot transport**, degree `e₄ + e₅`. -/
theorem botRoute_comp_bslot
    {k : ZMod 2} {y : (stdTower (K := K) b).carrier}
    (hy : y ∈ (stdTower (K := K) b).grading k)
    (ht5B : ∀ n : BL K a b (c + d), t₅ (y • n) = ((sgn (e₅ * k) : ℤˣ) : ℤ) • (y • t₅ n))
    (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (y • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (y • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [botRoute_apply, botRoute_apply,
    E4.comp_bslot_univ K a b c d e₄ t₄ ht₄ hy, map_zsmul,
    E5.comp_bslot_univ K a b c d e₅ t₅ ht₅ hy ht5B, map_zsmul, map_zsmul,
    Q4Close.comp_bslot_univ K a b c d hy, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`botRoute`'s `c`-slot transport**, degree `e₄ + e₅` — `E4`'s leg
needs `t₄`'s own `c`-slot equivariance, `E5`'s is a *spectator*,
`q4Close`'s is fully direct. -/
theorem botRoute_comp_cslot
    {k : ZMod 2} {z0 : (stdTower (K := K) c).carrier}
    (hz0 : z0 ∈ (stdTower (K := K) c).grading k)
    (ht4C : ∀ n : BL K (a + b) c d, t₄ (z0 • n) = ((sgn (e₄ * k) : ℤˣ) : ℤ) • (z0 • t₄ n))
    (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (z0 • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (z0 • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [botRoute_apply, botRoute_apply,
    E4.comp_cslot_univ K a b c d e₄ t₄ ht₄ hz0 ht4C, map_zsmul,
    E5.comp_cslot_univ K a b c d e₅ t₅ ht₅ hz0, map_zsmul, map_zsmul,
    Q4Close.comp_cslot_univ K a b c d, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`botRoute`'s `d`-slot transport**, degree `e₄ + e₅`. -/
theorem botRoute_comp_dslot
    {k : ZMod 2} {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading k)
    (ht4D : ∀ n : BL K (a + b) c d, t₄ (τ • n) = ((sgn (e₄ * k) : ℤˣ) : ℤ) • (τ • t₄ n))
    (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (τ • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (τ • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [botRoute_apply, botRoute_apply,
    E4.comp_dslot_univ K a b c d e₄ t₄ ht₄ hτ ht4D, map_zsmul,
    E5.comp_dslot_univ K a b c d e₅ t₅ ht₅ hτ, map_zsmul, map_zsmul,
    Q4Close.comp_dslot_univ K a b c d, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`botRoute`'s right-action transport**, along the composite
associativity recast `T_{a+b+c+d} ≅ T_{a+(b+c+d)}` threading through
`E4`'s, `E5`'s and `q4Close`'s own casts (which compose to the same
recast as `quadRightCast_eq`, `QuadInterSpace.lean`). -/
theorem botRoute_comp_right
    (τ : (stdTower (K := K) (a + b + c + d)).carrier)
    (ht4R : ∀ n : BL K (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((stdTowerCast (K := K)
              (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) • t₄ n)
    (ht5R : ∀ n : BL K a b (c + d),
      t₅ (MulOpposite.op
            ((stdTowerCast (K := K) (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) • n)
        = MulOpposite.op ((stdTowerCast (K := K) (botRoute_right_recast_eq5 a b c d)).toAlgEquiv
              ((stdTowerCast (K := K) (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ)) • t₅ n)
    (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (MulOpposite.op τ • z)
      = MulOpposite.op ((stdTowerCast (K := K)
            (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm
            ((stdTowerCast (K := K) (botRoute_right_recast_eq5 a b c d)).toAlgEquiv
              ((stdTowerCast (K := K) (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ)))
          • botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z := by
  rw [botRoute_apply, botRoute_apply,
    E4.comp_right_univ K a b c d e₄ t₄ ht₄ τ ht4R,
    E5.comp_right_univ K a b c d e₅ t₅ ht₅
      ((stdTowerCast (K := K) (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) ht5R,
    Q4Close.comp_right_univ K a b c d]

end BotRoute

end PentagonB

end Bimod

end Superfusion
