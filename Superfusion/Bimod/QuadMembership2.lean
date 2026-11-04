/-
Superfusion / Bimod / QuadMembership2

Milestone M8a-8c′-2c-iii (roadmap v3): **`homGrading` for both pentagon
routes, and the two `∈ quadInterSpace` membership statements** —
completing stage 2c of `QuadMembership.lean`.

`QuadMembership.lean` landed the five `K`-linear conditions (the four
slot super-equivariances and right-semilinearity) for `topRoute` and
`botRoute`, universal in the vertex argument, deferring the sixth
condition (`homGrading`, `f (ℳ i) ⊆ 𝒩 (i + d)`) for want of a
**degree-matching induction**: `RelTensor.induction_on_left_homog`
(the reusable helper behind every slot/right upgrade there) only
tracks *some* degree of the first factor, discarding the second
factor's degree entirely — too coarse for `homGrading`, which needs
the *sum* of both factors' degrees to match a prescribed target.

The core `Bimod.RelTensor` API supplies that finer induction:

* `RelTensor.induction_on_grading` — to prove a motive for every
  element of `M ⊗[A;K] N` of a prescribed `relGrading` degree `j`, it
  suffices to check `0`, the homogeneous generators `mk m n` with
  `m ∈ ℳ i`, `n ∈ 𝒩 k`, `i + k = j` (any *matching* pair, not a fixed
  one), and closure under addition and scalar multiples — obtained by
  routing `relGrading`'s own construction (the image, under the
  balancing quotient, of `tensorGrading`, M8a-3a/3b) through
  `tensorGrading`'s own degree-matching span induction
  (`tensorGrading_induction`, `GradedModule.lean`);
* `RelTensor.mem_of_grading` — the practically-used specialization to
  a `Submodule`-membership motive `F z ∈ S` (`F` a `K`-linear map, `S`
  a submodule of the codomain): `zero`/`add`/`smul`-closure come for
  free from `S` being a submodule, leaving only the homogeneous-
  generator check — this is exactly the idiom already spelled out by
  hand at `midEnd_mem_relGrading`, `leftActionEnd_mem_relGrading`,
  `rightActionEnd_mem_relGrading`, `map_mem_relGrading_of_degree`,
  `smap_mem_relGrading_of_degree` (`MiddleAction.lean`,
  `OuterActions.lean`, `MapEquivariance.lean`,
  `SignedMapEquivariance.lean`), factored into one reusable lemma.

This file applies those general lemmas to the five pentagon vertices;
it does not redeclare them in a pentagon-specific namespace.

Composing `RelTensor.mem_of_grading` twice — once at each vertex's own
outer `RelTensor` layer, once at the nested `B_L`/`B_R`-factor's layer
— gives, for each vertex `Q1`, `Q2`, `Q3`, `Q5`, `Q4r`, a "three-
generator, degree-summing" membership bridge (`Q1.mem_of_grading`,
etc.) through the vertex's own synonym `mk`s: to show `F z ∈ S` for
`z` of a prescribed vertex-grading degree `i`, it suffices to check it
on the fully-spelled generators `Vertex.mk (Factor.mk u v) w` with
`u`, `v`, `w` all homogeneous of degrees summing to `i` — exactly the
shape every edge's existing generator-level `mem_grading`
(`EdgeEquiv2.lean`–`EdgeEquivClose.lean`) is *already* stated in, so
composing them (with the degree-sum hypothesis feeding the *unused*
degree freedom of those lemmas) upgrades each to the universal form
`f (Vertex.grading i) ⊆ Vertex'.grading (i + e)` — `E2.mem_grading_univ`,
`E3.mem_grading_univ`, `E4.mem_grading_univ`, `E5.mem_grading_univ`,
`Q4Close.mem_grading_univ` (`E1.mem_grading`, `EdgeEquiv.lean`, is
already universal — general `RelTensor.map` descent, M8a-3b/7f).

Composing these five along the two routes (direct function composition,
no further induction, mirroring `QuadMembership.lean`'s own
`topRoute_comp_*`/`botRoute_comp_*`) gives `topRoute_mem_grading`,
`botRoute_mem_grading`, and finally, bundling them with
`QuadMembership.lean`'s five conditions via `mem_quadInterSpace_iff`,
the two completions of stage 2c: **`topRoute_mem`**, **`botRoute_mem`**
— both pentagon routes are homogeneous quadruple intertwiners, the
stage on which `χ_abs` (next milestone) is the unique scalar relating
them.
-/
import Superfusion.Bimod.QuadMembership

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

attribute [local instance 500] leftModule rightModule

/-! ### Vertex layer: degree-matching membership bridges

Composing `RelTensor.mem_of_grading` twice at each vertex (once at the
vertex's own outer `RelTensor` layer, once at the nested `B_L`/`B_R`
factor) gives, for each of the five vertices `Q1`, `Q2`, `Q3`, `Q5`,
`Q4r`, the "three-generator, degree-summing" membership bridge needed
to upgrade the corresponding edge's `mem_grading` to universal form. -/

/-- **Degree-matching membership bridge at `Q1`**: to show `F z ∈ S`
for `z` of a prescribed `Q1`-grading degree `i`, it suffices to check
it on the generators `Q1.mk (BL.mk u v) w` with `u`, `v`, `w` all
homogeneous of degrees summing to `i`. -/
theorem Q1.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : Q1 K a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : Q1 K a b c d} (hz : z ∈ Q1.grading K a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : TowerColumn K a b) (v : TowerColumn K (a + b) c)
      (w : TowerColumn K (a + b + c) d),
      u ∈ TowerColumn.grading K a b j → v ∈ TowerColumn.grading K (a + b) c jv →
      w ∈ TowerColumn.grading K (a + b + c) d jw → j + jv + jw = i →
      F (Q1.mk K a b c d (BL.mk K a b c u v) w) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading (BL.grading K a b c)
    (TowerColumn.grading K (a + b + c) d) F S hz ?_
  intro j' jw hjjw m w hm hw
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K a b)
    (TowerColumn.grading K (a + b) c) (F.comp ((Q1.mk K a b c d).flip w)) S hm ?_
  intro j jv hjjv u v hu hv
  show F (Q1.mk K a b c d (BL.mk K a b c u v) w) ∈ S
  exact homog u v w hu hv hw (by rw [hjjv, hjjw])

/-- **Degree-matching membership bridge at `Q2`**: through
`Q2.mk (BR.mk u v) w`. -/
theorem Q2.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : Q2 K a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : Q2 K a b c d} (hz : z ∈ Q2.grading K a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : TowerColumn K b c) (v : TowerColumn K a (b + c))
      (w : TowerColumn K (a + b + c) d),
      u ∈ TowerColumn.grading K b c j → v ∈ TowerColumn.grading K a (b + c) jv →
      w ∈ TowerColumn.grading K (a + b + c) d jw → j + jv + jw = i →
      F (Q2.mk K a b c d (BR.mk K a b c u v) w) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading (BR.grading K a b c)
    (TowerColumn.grading K (a + b + c) d) F S hz ?_
  intro j' jw hjjw m w hm hw
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K b c)
    (TowerColumn.grading K a (b + c)) (F.comp ((Q2.mk K a b c d).flip w)) S hm ?_
  intro j jv hjjv u v hu hv
  show F (Q2.mk K a b c d (BR.mk K a b c u v) w) ∈ S
  exact homog u v w hu hv hw (by rw [hjjv, hjjw])

/-- **Degree-matching membership bridge at `Q3`**: through
`Q3.mk u (BR.mk v w)` (`Q3Inner = B_R(a,b{+}c,d)`, so the *second*
factor is the one needing further decomposition). -/
theorem Q3.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : Q3 K a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : Q3 K a b c d} (hz : z ∈ Q3.grading K a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : TowerColumn K b c) (v : TowerColumn K (b + c) d)
      (w : TowerColumn K a ((b + c) + d)),
      u ∈ TowerColumn.grading K b c j → v ∈ TowerColumn.grading K (b + c) d jv →
      w ∈ TowerColumn.grading K a ((b + c) + d) jw → j + jv + jw = i →
      F (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K b c)
    (Q3Inner.grading K a b c d) F S hz ?_
  intro j jv' hjjv' u x hu hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K (b + c) d)
    (TowerColumn.grading K a ((b + c) + d)) (F.comp (Q3.mk K a b c d u)) S hx ?_
  intro jv jw hjvjw v w hv hw
  show F (Q3.mk K a b c d u (BR.mk K a (b + c) d v w)) ∈ S
  exact homog u v w hu hv hw
    (by rw [show j + jv + jw = j + (jv + jw) from by ring, hjvjw, hjjv'])

/-- **Degree-matching membership bridge at `Q5`**: through
`Q5.mk u (BR.mk v w)`. -/
theorem Q5.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : Q5 K a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : Q5 K a b c d} (hz : z ∈ Q5.grading K a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : TowerColumn K a b) (v : TowerColumn K c d)
      (w : TowerColumn K (a + b) (c + d)),
      u ∈ TowerColumn.grading K a b j → v ∈ TowerColumn.grading K c d jv →
      w ∈ TowerColumn.grading K (a + b) (c + d) jw → j + jv + jw = i →
      F (Q5.mk K a b c d u (BR.mk K (a + b) c d v w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K a b)
    (BR.grading K (a + b) c d) F S hz ?_
  intro j jv' hjjv' u x hu hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K c d)
    (TowerColumn.grading K (a + b) (c + d)) (F.comp (Q5.mk K a b c d u)) S hx ?_
  intro jv jw hjvjw v w hv hw
  show F (Q5.mk K a b c d u (BR.mk K (a + b) c d v w)) ∈ S
  exact homog u v w hu hv hw
    (by rw [show j + jv + jw = j + (jv + jw) from by ring, hjvjw, hjjv'])

/-- **Degree-matching membership bridge at `Q4r`**: through
`Q4r.mk v (BR.mk u w)`. -/
theorem Q4r.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : Q4r K a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : Q4r K a b c d} (hz : z ∈ Q4r.grading K a b c d i)
    (homog : ∀ {jv j jw : ZMod 2}
      (v : TowerColumn K c d) (u : TowerColumn K b (c + d))
      (w : TowerColumn K a (b + (c + d))),
      v ∈ TowerColumn.grading K c d jv → u ∈ TowerColumn.grading K b (c + d) j →
      w ∈ TowerColumn.grading K a (b + (c + d)) jw → jv + j + jw = i →
      F (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K c d)
    (BR.grading K a b (c + d)) F S hz ?_
  intro jv j' hjvj' v x hv hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (TowerColumn.grading K b (c + d))
    (TowerColumn.grading K a (b + (c + d))) (F.comp (Q4r.mk K a b c d v)) S hx ?_
  intro j jw hjjw u w hu hw
  show F (Q4r.mk K a b c d v (BR.mk K a b (c + d) u w)) ∈ S
  exact homog v u w hv hu hw
    (by rw [show jv + j + jw = jv + (j + jw) from by ring, hjjw, hjvj'])

/-! ### Edge `mem_grading`, upgraded to universal

Each edge's existing generator-level `mem_grading` (`EdgeEquiv2.lean`–
`EdgeEquivClose.lean`) already holds for *any* triple of homogeneous
generator degrees, unconstrained relative to each other — exactly the
freedom the vertex-layer `mem_of_grading` bridges above supply
(degrees summing to the *ambient* input degree `i`), so the upgrade to
the universal `homGrading`-shaped statement is direct composition, no
further induction. -/

namespace E2

variable (e : ZMod 2) (t₂ : Q2rInner K a b c d →ₗ[K] Q3Inner K a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (stdTower (K := K) (b + c)).carrier⦄,
  y ∈ (stdTower (K := K) (b + c)).grading i →
  ∀ n : Q2rInner K a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- **`E2` is homogeneous of `t₂`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn.grading K a (b + c)) (TowerColumn.grading K (a + b + c) d) jj,
        t₂ n ∈ Q3Inner.grading K a b c d (jj + e))
    {i : ZMod 2} {z : Q2 K a b c d} (hz : z ∈ Q2.grading K a b c d i) :
    E2 K a b c d e t₂ ht₂ z ∈ Q3.grading K a b c d (i + e) := by
  refine Q2.mem_of_grading K a b c d (E2 K a b c d e t₂ ht₂)
    (Q3.grading K a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K a b c d e t₂ ht₂ ht₂deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end E2

namespace E3

variable (t₃ : BL K b c d →ₗ[K] BR K b c d)
variable (ht₃ : ∀ (τ : (stdTower (K := K) (b + c + d)).carrier)
  (m : BL K b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- **`E3` is homogeneous of `t₃`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e))
    {i : ZMod 2} {z : Q3 K a b c d} (hz : z ∈ Q3.grading K a b c d i) :
    E3 K a b c d t₃ ht₃ z ∈ Q4.grading K a b c d (i + e) := by
  refine Q3.mem_of_grading K a b c d (E3 K a b c d t₃ ht₃)
    (Q4.grading K a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K a b c d t₃ ht₃ ht₃deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end E3

namespace E4

variable (e : ZMod 2) (t₄ : BL K (a + b) c d →ₗ[K] BR K (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (stdTower (K := K) (a + b)).carrier⦄,
  x ∈ (stdTower (K := K) (a + b)).grading i →
  ∀ n : BL K (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- **`E4` is homogeneous of `t₄`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₄deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K (a + b) c d j',
      t₄ n ∈ BR.grading K (a + b) c d (j' + e))
    {i : ZMod 2} {z : Q1 K a b c d} (hz : z ∈ Q1.grading K a b c d i) :
    E4 K a b c d e t₄ ht₄ z ∈ Q5.grading K a b c d (i + e) := by
  refine Q1.mem_of_grading K a b c d (E4 K a b c d e t₄ ht₄)
    (Q5.grading K a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K a b c d e t₄ ht₄ ht₄deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end E4

namespace E5

variable (e : ZMod 2) (t₅ : BL K a b (c + d) →ₗ[K] BR K a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (stdTower (K := K) (c + d)).carrier⦄,
  z ∈ (stdTower (K := K) (c + d)).grading i →
  ∀ n : BL K a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- **`E5` is homogeneous of `t₅`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₅deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K a b (c + d) j',
      t₅ n ∈ BR.grading K a b (c + d) (j' + e))
    {i : ZMod 2} {z : Q5 K a b c d} (hz : z ∈ Q5.grading K a b c d i) :
    E5 K a b c d e t₅ ht₅ z ∈ Q4r.grading K a b c d (i + e) := by
  refine Q5.mem_of_grading K a b c d (E5 K a b c d e t₅ ht₅)
    (Q4r.grading K a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K a b c d e t₅ ht₅ ht₅deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end E5

namespace Q4Close

/-- **`q4Close` is homogeneous of degree `0`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    {i : ZMod 2} {z : Q4r K a b c d} (hz : z ∈ Q4r.grading K a b c d i) :
    q4Close K a b c d z ∈ Q4.grading K a b c d i := by
  refine Q4r.mem_of_grading K a b c d (q4Close K a b c d).toLinearMap
    (Q4.grading K a b c d i) hz ?_
  intro jv j jw v u w hv hu hw hsum
  have h := mem_grading K a b c d hv hu hw
  rwa [show jv + (j + jw) = jv + j + jw from by ring, hsum] at h

end Q4Close

/-! ### `topRoute`'s `homGrading`, and its full membership

`topRoute = E3 ∘ E2 ∘ E1`'s `homGrading` is direct composition of
`E1.mem_grading` (already universal), `E2.mem_grading_univ`,
`E3.mem_grading_univ` above.  Bundling it with `QuadMembership.lean`'s
five `K`-linear conditions (`topRoute_comp_aslot`/`bslot`/`cslot`/
`dslot`/`right`) via `mem_quadInterSpace_iff` gives `topRoute_mem` —
the completion of stage 2c for the top route: `t₁ ∈ interSpace K a b c
e₁` and `t₃ ∈ interSpace K b c d e₃` supply, via `mem_interSpace_iff`,
every one of `t₁`'s and `t₃`'s own slot/homogeneity data at once (the
design anticipated by `QuadMembership.lean`'s own `TopRoute` docstring);
`t₂`'s remaining data (its `a`-, `d`-slot equivariances, its right-
equivariance, and its own degree-`e₂` homogeneity) has no such bundle
at `Q2rInner`/`Q3Inner`'s level, so it is taken raw. -/

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

/-- The associativity recast of the total coefficient algebra used by
`topRoute_mem`'s `ht2R` (matches `QuadMembership.lean`'s private
`topRoute_right_recast_eq`, re-proved here since `private` names do
not cross files — the propositions coincide, so the resulting casts
agree by proof irrelevance). -/
private theorem topRoute_right_recast_eq2 : a + b + c + d = a + (b + c + d) := by ring

/-- The `topRoute = E3 ∘ E2 ∘ E1` composite, unfolded (matches
`QuadMembership.lean`'s private `topRoute_apply`, re-derived here since
`private` declarations do not cross files). -/
private theorem topRoute_apply' (z : Q1 K a b c d) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      = E3 K a b c d t₃ ht₃
          (E2 K a b c d e₂ t₂ ht₂ (E1 K a b c d t₁ ht₁ z)) := by
  show (E3 K a b c d t₃ ht₃ ∘ₗ E2 K a b c d e₂ t₂ ht₂ ∘ₗ E1 K a b c d t₁ ht₁) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]

/-- **`topRoute`'s `homGrading`**, degree `e₁ + e₂ + e₃` — direct
composition of `E1.mem_grading`, `E2.mem_grading_univ`,
`E3.mem_grading_univ`. -/
theorem topRoute_mem_grading
    {e₁ e₃ : ZMod 2}
    (hte1 : ∀ j : ZMod 2, ∀ m ∈ BL.grading K a b c j,
      t₁ m ∈ BR.grading K a b c (j + e₁))
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn.grading K a (b + c)) (TowerColumn.grading K (a + b + c) d) jj,
        t₂ n ∈ Q3Inner.grading K a b c d (jj + e₂))
    (ht3deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K b c d j',
      t₃ n ∈ BR.grading K b c d (j' + e₃))
    {i : ZMod 2} {z : Q1 K a b c d} (hz : z ∈ Q1.grading K a b c d i) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      ∈ Q4.grading K a b c d (i + (e₁ + e₂ + e₃)) := by
  rw [topRoute_apply']
  have h1 := E1.mem_grading K a b c d t₁ ht₁ hte1 hz
  have h2 := E2.mem_grading_univ K a b c d e₂ t₂ ht₂ ht₂deg h1
  have h3 := E3.mem_grading_univ K a b c d t₃ ht₃ ht3deg h2
  rwa [show i + e₁ + e₂ + e₃ = i + (e₁ + e₂ + e₃) from by ring] at h3

/-- **`topRoute` is a homogeneous degree-`(e₁ + e₂ + e₃)` quadruple
intertwiner**, given `t₁ ∈ interSpace K a b c e₁`, `t₃ ∈ interSpace K b
c d e₃` (bundling, via `mem_interSpace_iff`, every one of `t₁`'s and
`t₃`'s slot/right/homogeneity data at once), and `t₂`'s own remaining
`a`-, `d`-slot equivariances, right-equivariance and degree-`e₂`
homogeneity — the completion of stage 2c for the top route. -/
theorem topRoute_mem
    {e₁ e₃ : ZMod 2}
    (ht1 : t₁ ∈ interSpace K a b c e₁)
    (ht2A : ∀ ⦃k : ZMod 2⦄ ⦃x : (stdTower (K := K) a).carrier⦄,
      x ∈ (stdTower (K := K) a).grading k →
      ∀ (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
        t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
              (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) (x • v) w)
          = ((sgn (e₂ * k) : ℤˣ) : ℤ) •
              (x • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
                (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w)))
    (ht2D : ∀ ⦃m : ZMod 2⦄ ⦃τ : (stdTower (K := K) d).carrier⦄,
      τ ∈ (stdTower (K := K) d).grading m →
      ∀ x : Q2rInner K a b c d,
        t₂ (τ • x) = ((sgn (e₂ * m) : ℤˣ) : ℤ) • (τ • t₂ x))
    (ht2R : ∀ (τ : (stdTower (K := K) (a + b + c + d)).carrier)
      (v : TowerColumn K a (b + c)) (w : TowerColumn K (a + b + c) d),
      t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((stdTowerCast (K := K) (topRoute_right_recast_eq2 a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (stdTower (K := K) (a + b + c)).carrier
            (TowerColumn K a (b + c)) (TowerColumn K (a + b + c) d) v w))
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (stdTower (K := K) (a + b + c)).carrier
          (TowerColumn.grading K a (b + c)) (TowerColumn.grading K (a + b + c) d) jj,
        t₂ n ∈ Q3Inner.grading K a b c d (jj + e₂))
    (ht3 : t₃ ∈ interSpace K b c d e₃) :
    topRoute K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      ∈ quadInterSpace K a b c d (e₁ + e₂ + e₃) := by
  obtain ⟨hg1, heqA1, heqB1, heqC1, -⟩ := (mem_interSpace_iff K a b c).mp ht1
  obtain ⟨hg3, heqA3, heqB3, heqC3, -⟩ := (mem_interSpace_iff K b c d).mp ht3
  have ht1A := (mem_superEquivariant (stdTower (K := K) a).grading).mp heqA1
  have ht1B := (mem_superEquivariant (stdTower (K := K) b).grading).mp heqB1
  have ht1C := (mem_superEquivariant (stdTower (K := K) c).grading).mp heqC1
  have hte1 := (mem_homGrading (BL.grading K a b c) (BR.grading K a b c)).mp hg1
  have ht3B := (mem_superEquivariant (stdTower (K := K) b).grading).mp heqA3
  have ht3C := (mem_superEquivariant (stdTower (K := K) c).grading).mp heqB3
  have ht3D := (mem_superEquivariant (stdTower (K := K) d).grading).mp heqC3
  have ht3deg := (mem_homGrading (BL.grading K b c d) (BR.grading K b c d)).mp hg3
  refine (mem_quadInterSpace_iff K a b c d).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mem_homGrading (Q1.grading K a b c d) (Q4.grading K a b c d)).mpr ?_
    intro i z hz
    exact topRoute_mem_grading K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hte1 ht₂deg ht3deg hz
  · refine (mem_superEquivariant (stdTower (K := K) a).grading).mpr ?_
    intro k x hx z
    exact topRoute_comp_aslot K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hx (ht1A hx) (ht2A hx) ht3deg z
  · refine (mem_superEquivariant (stdTower (K := K) b).grading).mpr ?_
    intro k y hy z
    exact topRoute_comp_bslot K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hy (ht1B hy) (ht3B hy) z
  · refine (mem_superEquivariant (stdTower (K := K) c).grading).mpr ?_
    intro k z0 hz0 z
    exact topRoute_comp_cslot K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hz0 (ht1C hz0) (ht3C hz0) z
  · refine (mem_superEquivariant (stdTower (K := K) d).grading).mpr ?_
    intro k τ hτ z
    exact topRoute_comp_dslot K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hτ hte1 (ht2D hτ) (ht3D hτ) z
  · refine (mem_rightSemilinear
      ((stdTowerCast (K := K) (topRoute_right_recast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom)).mpr ?_
    intro τ z
    exact topRoute_comp_right K a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ τ (ht2R τ) z

end TopRoute

/-! ### `botRoute`'s `homGrading`, and its full membership

`botRoute = q4Close ∘ E5 ∘ E4`'s `homGrading` is direct composition of
`E4.mem_grading_univ`, `E5.mem_grading_univ`, `Q4Close.mem_grading_univ`
above (`q4Close` itself is degree-`0`).  Bundling it with
`QuadMembership.lean`'s five `K`-linear conditions with
`t₄ ∈ interSpace K (a+b) c d e₄`, `t₅ ∈ interSpace K a b (c+d) e₅`
supplying every piece of `t₄`'s and `t₅`'s own slot/right/homogeneity
data needs two composed `stdTowerCast`s to collapse to the single cast
`quadInterSpace`'s own right-semilinearity condition is stated
against — general helper lemmas for `stdTowerCast`'s composition
(`stdTowerCast_trans`, `stdTowerCast_symm_apply`), proved by `subst`
along the (fresh, universally quantified) index equalities. -/

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

/-- Two composed `stdTowerCast`s along a chain `x = y = z` collapse to
the single cast along the transitivity — proved by `subst` along the
(fresh, universally quantified) index equalities. -/
private theorem stdTowerCast_trans {x y z : ZMod 8} (h1 : x = y) (h2 : y = z)
    (τ : (stdTower (K := K) x).carrier) :
    (stdTowerCast (K := K) h2).toAlgEquiv ((stdTowerCast (K := K) h1).toAlgEquiv τ)
      = (stdTowerCast (K := K) (h1.trans h2)).toAlgEquiv τ := by
  subst h1; subst h2; rfl

/-- `stdTowerCast`'s inverse is the cast along the symmetric
equality. -/
private theorem stdTowerCast_symm_apply {x y : ZMod 8} (h : x = y)
    (τ : (stdTower (K := K) y).carrier) :
    (stdTowerCast (K := K) h).toAlgEquiv.symm τ = (stdTowerCast (K := K) h.symm).toAlgEquiv τ := by
  subst h; rfl

/-- The `botRoute = q4Close ∘ E5 ∘ E4` composite, unfolded (matches
`QuadMembership.lean`'s private `botRoute_apply`). -/
private theorem botRoute_apply' (z : Q1 K a b c d) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      = q4Close K a b c d
          (E5 K a b c d e₅ t₅ ht₅ (E4 K a b c d e₄ t₄ ht₄ z)) := by
  show ((q4Close K a b c d).toLinearMap ∘ₗ E5 K a b c d e₅ t₅ ht₅
      ∘ₗ E4 K a b c d e₄ t₄ ht₄) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-- **`botRoute`'s `homGrading`**, degree `e₄ + e₅` — direct
composition of `E4.mem_grading_univ`, `E5.mem_grading_univ`,
`Q4Close.mem_grading_univ`. -/
theorem botRoute_mem_grading
    (ht4deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K (a + b) c d j',
      t₄ n ∈ BR.grading K (a + b) c d (j' + e₄))
    (ht5deg : ∀ j' : ZMod 2, ∀ n ∈ BL.grading K a b (c + d) j',
      t₅ n ∈ BR.grading K a b (c + d) (j' + e₅))
    {i : ZMod 2} {z : Q1 K a b c d} (hz : z ∈ Q1.grading K a b c d i) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      ∈ Q4.grading K a b c d (i + (e₄ + e₅)) := by
  rw [botRoute_apply']
  have h1 := E4.mem_grading_univ K a b c d e₄ t₄ ht₄ ht4deg hz
  have h2 := E5.mem_grading_univ K a b c d e₅ t₅ ht₅ ht5deg h1
  have h3 := Q4Close.mem_grading_univ K a b c d h2
  rwa [show i + e₄ + e₅ = i + (e₄ + e₅) from by ring] at h3

/-- The associativity recasts used by `botRoute_mem`'s `ht4R`/`ht5R`
(match `QuadMembership.lean`'s private `botRoute_right_recast_eq4`/
`botRoute_right_recast_eq5`, re-proved here since `private` names do
not cross files). -/
private theorem botRoute_right_recast_eq4' : a + b + c + d = a + b + (c + d) := by ring

private theorem botRoute_right_recast_eq5' : a + b + (c + d) = a + (b + (c + d)) := by ring

private theorem botRoute_right_recast_eqF' : a + (b + c + d) = a + (b + (c + d)) :=
  congrArg (a + ·) (add_assoc b c d)

/-- The three composed `stdTowerCast`s of `botRoute_comp_right` collapse
to the single cast `quadInterSpace`'s own right-semilinearity condition
is stated against (both prove `a + b + c + d = a + (b + c + d)`, so the
resulting casts agree by proof irrelevance once collapsed to one). -/
private theorem botRoute_right_cast_eq' : a + b + c + d = a + (b + c + d) := by ring

private theorem botRoute_right_cast_apply' (τ : (stdTower (K := K) (a + b + c + d)).carrier) :
    (stdTowerCast (K := K) (botRoute_right_recast_eqF' a b c d)).toAlgEquiv.symm
        ((stdTowerCast (K := K) (botRoute_right_recast_eq5' a b c d)).toAlgEquiv
          ((stdTowerCast (K := K) (botRoute_right_recast_eq4' a b c d)).toAlgEquiv τ))
      = (stdTowerCast (K := K) (botRoute_right_cast_eq' a b c d)).toAlgEquiv τ := by
  rw [stdTowerCast_symm_apply, stdTowerCast_trans, stdTowerCast_trans]

/-- **`botRoute` is a homogeneous degree-`(e₄ + e₅)` quadruple
intertwiner**, given `t₄ ∈ interSpace K (a+b) c d e₄`, `t₅ ∈ interSpace
K a b (c+d) e₅` (bundling, via `mem_interSpace_iff`, every one of
`t₄`'s and `t₅`'s slot/right/homogeneity data at once) — the completion
of stage 2c for the bottom route. -/
theorem botRoute_mem
    (ht4 : t₄ ∈ interSpace K (a + b) c d e₄)
    (ht5 : t₅ ∈ interSpace K a b (c + d) e₅) :
    botRoute K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅
      ∈ quadInterSpace K a b c d (e₄ + e₅) := by
  obtain ⟨hg4, -, heqB4, heqC4, hR4⟩ := (mem_interSpace_iff K (a + b) c d).mp ht4
  obtain ⟨hg5, heqA5, heqB5, -, hR5⟩ := (mem_interSpace_iff K a b (c + d)).mp ht5
  have ht4C := (mem_superEquivariant (stdTower (K := K) c).grading).mp heqB4
  have ht4D := (mem_superEquivariant (stdTower (K := K) d).grading).mp heqC4
  have ht4deg := (mem_homGrading (BL.grading K (a + b) c d) (BR.grading K (a + b) c d)).mp hg4
  have ht5A := (mem_superEquivariant (stdTower (K := K) a).grading).mp heqA5
  have ht5B := (mem_superEquivariant (stdTower (K := K) b).grading).mp heqB5
  have ht5deg := (mem_homGrading (BL.grading K a b (c + d)) (BR.grading K a b (c + d))).mp hg5
  have ht4R := (mem_rightSemilinear
    (stdTowerCast (K := K) (botRoute_right_recast_eq4' a b c d)).toAlgEquiv.toAlgHom.toRingHom).mp hR4
  have ht5R := (mem_rightSemilinear
    (stdTowerCast (K := K) (botRoute_right_recast_eq5' a b c d)).toAlgEquiv.toAlgHom.toRingHom).mp hR5
  refine (mem_quadInterSpace_iff K a b c d).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mem_homGrading (Q1.grading K a b c d) (Q4.grading K a b c d)).mpr ?_
    intro i z hz
    exact botRoute_mem_grading K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ht4deg ht5deg hz
  · refine (mem_superEquivariant (stdTower (K := K) a).grading).mpr ?_
    intro k x hx z
    exact botRoute_comp_aslot K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hx (ht5A hx) z
  · refine (mem_superEquivariant (stdTower (K := K) b).grading).mpr ?_
    intro k y hy z
    exact botRoute_comp_bslot K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hy (ht5B hy) z
  · refine (mem_superEquivariant (stdTower (K := K) c).grading).mpr ?_
    intro k z0 hz0 z
    exact botRoute_comp_cslot K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hz0 (ht4C hz0) z
  · refine (mem_superEquivariant (stdTower (K := K) d).grading).mpr ?_
    intro k τ hτ z
    exact botRoute_comp_dslot K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hτ (ht4D hτ) z
  · refine (mem_rightSemilinear
      ((stdTowerCast (K := K) (botRoute_right_cast_eq' a b c d)).toAlgEquiv.toAlgHom.toRingHom)).mpr ?_
    intro τ z
    have h := botRoute_comp_right K a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ τ (ht4R τ)
      (fun n => ht5R ((stdTowerCast (K := K) (botRoute_right_recast_eq4' a b c d)).toAlgEquiv τ) n) z
    rwa [botRoute_right_cast_apply'] at h

end BotRoute

end PentagonB

end Bimod

end Superfusion
