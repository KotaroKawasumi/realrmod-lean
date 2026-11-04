/-
Superfusion / GaugeChi / PentagonRouteMembership

Milestone M12-4 of the abstract `(p, χ)` arc (continued and completed):
**`homGrading` for both pentagon routes, and the two `∈ gQuadInterSpace`
membership statements** — the Γ-mirror of `Superfusion.Bimod.
QuadMembership2`, completing `GaugeChi.PentagonRouteEquiv`'s five
`K`-linear conditions with the sixth (`homGrading`).

The degree-matching induction `RelTensor.induction_on_grading` and its
`Submodule`-membership specialization `RelTensor.mem_of_grading`
(`Superfusion.Bimod.RelTensor`) are *already general* (over an arbitrary balanced
tensor `M ⊗[A] N`), so they are reused **verbatim** here; only the
vertex-level "three-generator, degree-summing" membership bridges
(`GQ1.mem_of_grading`, …) threading them through each vertex's own synonym
`mk` are transcribed.  Composing them upgrades each edge's `mem_grading`
(generator-∀) to the universal `homGrading`-shaped statement
`GE2.mem_grading_univ`, …, `GQ4Close.mem_grading_univ` (`GE1.mem_grading` is
already universal); composing THOSE along the two routes gives
`gTopRoute_mem_grading`, `gBotRoute_mem_grading`, and finally, bundling them
with `PentagonRouteEquiv.lean`'s five conditions via
`mem_gQuadInterSpace_iff`, **`gTopRoute_mem`** and **`gBotRoute_mem`** —
both pentagon routes are homogeneous quadruple intertwiners.
-/
import Superfusion.GaugeChi.PentagonRouteEquiv

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

attribute [local instance 500] leftModule rightModule

/-! ### Vertex layer: degree-matching membership bridges -/

/-- **Degree-matching membership bridge at `GQ1`**: to show `F z ∈ S` for
`z` of a prescribed `GQ1`-grading degree `i`, it suffices to check it on
the generators `GQ1.mk (GBL.mk u v) w` with `u`, `v`, `w` all homogeneous
of degrees summing to `i`. -/
theorem GQ1.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : GQ1 K Γ a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : GQ1 K Γ a b c d} (hz : z ∈ GQ1.grading K Γ a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
      (w : FusionColumn (Γ.fuse (a + b + c) d)),
      u ∈ FusionColumn.grading (Γ.fuse a b) j → v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv →
      w ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) jw → j + jv + jw = i →
      F (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading (GBL.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d)) F S hz ?_
  intro j' jw hjjw m w hm hw
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse a b))
    (FusionColumn.grading (Γ.fuse (a + b) c)) (F.comp ((GQ1.mk K Γ a b c d).flip w)) S hm ?_
  intro j jv hjjv u v hu hv
  show F (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w) ∈ S
  exact homog u v w hu hv hw (by rw [hjjv, hjjw])

/-- **Degree-matching membership bridge at `GQ2`**: through
`GQ2.mk (GBR.mk u v) w`. -/
theorem GQ2.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : GQ2 K Γ a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : GQ2 K Γ a b c d} (hz : z ∈ GQ2.grading K Γ a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
      (w : FusionColumn (Γ.fuse (a + b + c) d)),
      u ∈ FusionColumn.grading (Γ.fuse b c) j → v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv →
      w ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) jw → j + jv + jw = i →
      F (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading (GBR.grading Γ a b c)
    (FusionColumn.grading (Γ.fuse (a + b + c) d)) F S hz ?_
  intro j' jw hjjw m w hm hw
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse b c))
    (FusionColumn.grading (Γ.fuse a (b + c))) (F.comp ((GQ2.mk K Γ a b c d).flip w)) S hm ?_
  intro j jv hjjv u v hu hv
  show F (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w) ∈ S
  exact homog u v w hu hv hw (by rw [hjjv, hjjw])

/-- **Degree-matching membership bridge at `GQ3`**: through
`GQ3.mk u (GBR.mk v w)`. -/
theorem GQ3.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : GQ3 K Γ a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : GQ3 K Γ a b c d} (hz : z ∈ GQ3.grading K Γ a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
      (w : FusionColumn (Γ.fuse a (b + c + d))),
      u ∈ FusionColumn.grading (Γ.fuse b c) j → v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv →
      w ∈ FusionColumn.grading (Γ.fuse a (b + c + d)) jw → j + jv + jw = i →
      F (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse b c))
    (GQ3Inner.grading K Γ a b c d) F S hz ?_
  intro j jv' hjjv' u x hu hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse (b + c) d))
    (FusionColumn.grading (Γ.fuse a (b + c + d))) (F.comp (GQ3.mk K Γ a b c d u)) S hx ?_
  intro jv jw hjvjw v w hv hw
  show F (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)) ∈ S
  exact homog u v w hu hv hw
    (by rw [show j + jv + jw = j + (jv + jw) from by ring, hjvjw, hjjv'])

/-- **Degree-matching membership bridge at `GQ5`**: through
`GQ5.mk u (GBR.mk v w)`. -/
theorem GQ5.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : GQ5 K Γ a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : GQ5 K Γ a b c d} (hz : z ∈ GQ5.grading K Γ a b c d i)
    (homog : ∀ {j jv jw : ZMod 2}
      (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse c d))
      (w : FusionColumn (Γ.fuse (a + b) (c + d))),
      u ∈ FusionColumn.grading (Γ.fuse a b) j → v ∈ FusionColumn.grading (Γ.fuse c d) jv →
      w ∈ FusionColumn.grading (Γ.fuse (a + b) (c + d)) jw → j + jv + jw = i →
      F (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse a b))
    (GBR.grading Γ (a + b) c d) F S hz ?_
  intro j jv' hjjv' u x hu hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse c d))
    (FusionColumn.grading (Γ.fuse (a + b) (c + d))) (F.comp (GQ5.mk K Γ a b c d u)) S hx ?_
  intro jv jw hjvjw v w hv hw
  show F (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)) ∈ S
  exact homog u v w hu hv hw
    (by rw [show j + jv + jw = j + (jv + jw) from by ring, hjvjw, hjjv'])

/-- **Degree-matching membership bridge at `GQ4r`**: through
`GQ4r.mk v (GBR.mk u w)`. -/
theorem GQ4r.mem_of_grading
    {P : Type*} [AddCommGroup P] [Module K P]
    (F : GQ4r K Γ a b c d →ₗ[K] P) (S : Submodule K P)
    {i : ZMod 2} {z : GQ4r K Γ a b c d} (hz : z ∈ GQ4r.grading K Γ a b c d i)
    (homog : ∀ {jv j jw : ZMod 2}
      (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
      (w : FusionColumn (Γ.fuse a (b + (c + d)))),
      v ∈ FusionColumn.grading (Γ.fuse c d) jv → u ∈ FusionColumn.grading (Γ.fuse b (c + d)) j →
      w ∈ FusionColumn.grading (Γ.fuse a (b + (c + d))) jw → jv + j + jw = i →
      F (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) ∈ S) :
    F z ∈ S := by
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse c d))
    (GBR.grading Γ a b (c + d)) F S hz ?_
  intro jv j' hjvj' v x hv hx
  refine Superfusion.Bimod.RelTensor.mem_of_grading
    (FusionColumn.grading (Γ.fuse b (c + d)))
    (FusionColumn.grading (Γ.fuse a (b + (c + d)))) (F.comp (GQ4r.mk K Γ a b c d v)) S hx ?_
  intro j jw hjjw u w hu hw
  show F (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) ∈ S
  exact homog v u w hv hu hw
    (by rw [show jv + j + jw = jv + (j + jw) from by ring, hjjw, hjvj'])

/-! ### Edge `mem_grading`, upgraded to universal -/

namespace GE2

variable (e : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
  y ∈ (Γ.D (b + c)).grading i →
  ∀ n : GQ2rInner K Γ a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- **`GE2` is homogeneous of `t₂`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (Γ.D (a + b + c)).carrier
          (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d)) jj,
        t₂ n ∈ GQ3Inner.grading K Γ a b c d (jj + e))
    {i : ZMod 2} {z : GQ2 K Γ a b c d} (hz : z ∈ GQ2.grading K Γ a b c d i) :
    GE2 K Γ a b c d e t₂ ht₂ z ∈ GQ3.grading K Γ a b c d (i + e) := by
  refine GQ2.mem_of_grading K Γ a b c d (GE2 K Γ a b c d e t₂ ht₂)
    (GQ3.grading K Γ a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K Γ a b c d e t₂ ht₂ ht₂deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end GE2

namespace GE3

variable (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
variable (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- **`GE3` is homogeneous of `t₃`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e))
    {i : ZMod 2} {z : GQ3 K Γ a b c d} (hz : z ∈ GQ3.grading K Γ a b c d i) :
    GE3 K Γ a b c d t₃ ht₃ z ∈ GQ4.grading K Γ a b c d (i + e) := by
  refine GQ3.mem_of_grading K Γ a b c d (GE3 K Γ a b c d t₃ ht₃)
    (GQ4.grading K Γ a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K Γ a b c d t₃ ht₃ ht₃deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end GE3

namespace GE4

variable (e : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
  x ∈ (Γ.D (a + b)).grading i →
  ∀ n : GBL Γ (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- **`GE4` is homogeneous of `t₄`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₄deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ (a + b) c d j',
      t₄ n ∈ GBR.grading Γ (a + b) c d (j' + e))
    {i : ZMod 2} {z : GQ1 K Γ a b c d} (hz : z ∈ GQ1.grading K Γ a b c d i) :
    GE4 K Γ a b c d e t₄ ht₄ z ∈ GQ5.grading K Γ a b c d (i + e) := by
  refine GQ1.mem_of_grading K Γ a b c d (GE4 K Γ a b c d e t₄ ht₄)
    (GQ5.grading K Γ a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K Γ a b c d e t₄ ht₄ ht₄deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end GE4

namespace GE5

variable (e : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
  z ∈ (Γ.D (c + d)).grading i →
  ∀ n : GBL Γ a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- **`GE5` is homogeneous of `t₅`'s degree `e`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    (ht₅deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ a b (c + d) j',
      t₅ n ∈ GBR.grading Γ a b (c + d) (j' + e))
    {i : ZMod 2} {z : GQ5 K Γ a b c d} (hz : z ∈ GQ5.grading K Γ a b c d i) :
    GE5 K Γ a b c d e t₅ ht₅ z ∈ GQ4r.grading K Γ a b c d (i + e) := by
  refine GQ5.mem_of_grading K Γ a b c d (GE5 K Γ a b c d e t₅ ht₅)
    (GQ4r.grading K Γ a b c d (i + e)) hz ?_
  intro j jv jw u v w hu hv hw hsum
  have h := mem_grading K Γ a b c d e t₅ ht₅ ht₅deg hu hv hw
  rwa [show j + (jv + jw + e) = j + jv + jw + e from by ring, hsum] at h

end GE5

namespace GQ4Close

/-- **`gq4Close` is homogeneous of degree `0`, universal in the vertex
argument.** -/
theorem mem_grading_univ
    {i : ZMod 2} {z : GQ4r K Γ a b c d} (hz : z ∈ GQ4r.grading K Γ a b c d i) :
    gq4Close K Γ a b c d z ∈ GQ4.grading K Γ a b c d i := by
  refine GQ4r.mem_of_grading K Γ a b c d (gq4Close K Γ a b c d).toLinearMap
    (GQ4.grading K Γ a b c d i) hz ?_
  intro jv j jw v u w hv hu hw hsum
  have h := mem_grading K Γ a b c d hv hu hw
  rwa [show jv + (j + jw) = jv + j + jw from by ring, hsum] at h

end GQ4Close

/-! ### `gTopRoute`'s `homGrading`, and its full membership

`gTopRoute = GE3 ∘ GE2 ∘ GE1`'s `homGrading` is direct composition of
`GE1.mem_grading` (already universal), `GE2.mem_grading_univ`,
`GE3.mem_grading_univ` above.  Bundling it with `PentagonRouteEquiv.lean`'s
five `K`-linear conditions via `mem_gQuadInterSpace_iff` gives
`gTopRoute_mem`: `t₁ ∈ gInterSpace Γ a b c e₁` and
`t₃ ∈ gInterSpace Γ b c d e₃` supply, via `mem_gInterSpace_iff`, every one
of `t₁`'s and `t₃`'s own slot/homogeneity data at once; `t₂`'s remaining
data (its `a`-, `d`-slot equivariances, its right-equivariance, and its own
degree-`e₂` homogeneity) has no such bundle at `GQ2rInner`/`GQ3Inner`'s
level, so it is taken raw. -/

section TopRoute

variable (t₁ : GBL Γ a b c →ₗ[K] GBR Γ a b c)
variable (ht₁ : ∀ (τ : (Γ.D (a + b + c)).carrier)
  (m : GBL Γ a b c), t₁ (MulOpposite.op τ • m) = MulOpposite.op τ • t₁ m)
variable (e₂ : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
  y ∈ (Γ.D (b + c)).grading i →
  ∀ n : GQ2rInner K Γ a b c d,
    t₂ (y • n) = ((sgn (e₂ * i) : ℤˣ) : ℤ) • (y • t₂ n))
variable (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
variable (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier)
  (m : GBL Γ b c d), t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- The associativity recast used by `gTopRoute_mem`'s `ht2R`. -/
private theorem topRoute_right_recast_eq2 : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- The `gTopRoute = GE3 ∘ GE2 ∘ GE1` composite, unfolded. -/
private theorem gTopRoute_apply' (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      = GE3 K Γ a b c d t₃ ht₃
          (GE2 K Γ a b c d e₂ t₂ ht₂ (GE1 K Γ a b c d t₁ ht₁ z)) := by
  show (GE3 K Γ a b c d t₃ ht₃ ∘ₗ GE2 K Γ a b c d e₂ t₂ ht₂ ∘ₗ GE1 K Γ a b c d t₁ ht₁) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]

/-- **`gTopRoute`'s `homGrading`**, degree `e₁ + e₂ + e₃`. -/
theorem gTopRoute_mem_grading
    {e₁ e₃ : ZMod 2}
    (hte1 : ∀ j : ZMod 2, ∀ m ∈ GBL.grading Γ a b c j,
      t₁ m ∈ GBR.grading Γ a b c (j + e₁))
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (Γ.D (a + b + c)).carrier
          (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d)) jj,
        t₂ n ∈ GQ3Inner.grading K Γ a b c d (jj + e₂))
    (ht3deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e₃))
    {i : ZMod 2} {z : GQ1 K Γ a b c d} (hz : z ∈ GQ1.grading K Γ a b c d i) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      ∈ GQ4.grading K Γ a b c d (i + (e₁ + e₂ + e₃)) := by
  rw [gTopRoute_apply']
  have h1 := GE1.mem_grading K Γ a b c d t₁ ht₁ hte1 hz
  have h2 := GE2.mem_grading_univ K Γ a b c d e₂ t₂ ht₂ ht₂deg h1
  have h3 := GE3.mem_grading_univ K Γ a b c d t₃ ht₃ ht3deg h2
  rwa [show i + e₁ + e₂ + e₃ = i + (e₁ + e₂ + e₃) from by ring] at h3

/-- **`gTopRoute` is a homogeneous degree-`(e₁ + e₂ + e₃)` quadruple
intertwiner**, given `t₁ ∈ gInterSpace Γ a b c e₁`, `t₃ ∈ gInterSpace Γ b c
d e₃`, and `t₂`'s own remaining `a`-, `d`-slot equivariances,
right-equivariance and degree-`e₂` homogeneity. -/
theorem gTopRoute_mem
    {e₁ e₃ : ZMod 2}
    (ht1 : t₁ ∈ gInterSpace K Γ a b c e₁)
    (ht2A : ∀ ⦃k : ZMod 2⦄ ⦃x : (Γ.D a).carrier⦄,
      x ∈ (Γ.D a).grading k →
      ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
        t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w)
          = ((sgn (e₂ * k) : ℤˣ) : ℤ) •
              (x • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))
    (ht2D : ∀ ⦃m : ZMod 2⦄ ⦃τ : (Γ.D d).carrier⦄,
      τ ∈ (Γ.D d).grading m →
      ∀ x : GQ2rInner K Γ a b c d,
        t₂ (τ • x) = ((sgn (e₂ * m) : ℤˣ) : ℤ) • (τ • t₂ x))
    (ht2R : ∀ (τ : (Γ.D (a + b + c + d)).carrier)
      (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((Γ.gaugeCast (topRoute_right_recast_eq2 a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (Γ.D (a + b + c)).carrier
          (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d)) jj,
        t₂ n ∈ GQ3Inner.grading K Γ a b c d (jj + e₂))
    (ht3 : t₃ ∈ gInterSpace K Γ b c d e₃) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃
      ∈ gQuadInterSpace K Γ a b c d (e₁ + e₂ + e₃) := by
  obtain ⟨hg1, heqA1, heqB1, heqC1, -⟩ := (mem_gInterSpace_iff K Γ a b c).mp ht1
  obtain ⟨hg3, heqA3, heqB3, heqC3, -⟩ := (mem_gInterSpace_iff K Γ b c d).mp ht3
  have ht1A := (mem_superEquivariant (Γ.D a).grading).mp heqA1
  have ht1B := (mem_superEquivariant (Γ.D b).grading).mp heqB1
  have ht1C := (mem_superEquivariant (Γ.D c).grading).mp heqC1
  have hte1 := (mem_homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c)).mp hg1
  have ht3B := (mem_superEquivariant (Γ.D b).grading).mp heqA3
  have ht3C := (mem_superEquivariant (Γ.D c).grading).mp heqB3
  have ht3D := (mem_superEquivariant (Γ.D d).grading).mp heqC3
  have ht3deg := (mem_homGrading (GBL.grading Γ b c d) (GBR.grading Γ b c d)).mp hg3
  refine (mem_gQuadInterSpace_iff K Γ a b c d).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mem_homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d)).mpr ?_
    intro i z hz
    exact gTopRoute_mem_grading K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hte1 ht₂deg ht3deg hz
  · refine (mem_superEquivariant (Γ.D a).grading).mpr ?_
    intro k x hx z
    exact gTopRoute_comp_aslot K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hx (ht1A hx) (ht2A hx) ht3deg z
  · refine (mem_superEquivariant (Γ.D b).grading).mpr ?_
    intro k y hy z
    exact gTopRoute_comp_bslot K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hy (ht1B hy) (ht3B hy) z
  · refine (mem_superEquivariant (Γ.D c).grading).mpr ?_
    intro k z0 hz0 z
    exact gTopRoute_comp_cslot K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hz0 (ht1C hz0) (ht3C hz0) z
  · refine (mem_superEquivariant (Γ.D d).grading).mpr ?_
    intro k τ hτ z
    exact gTopRoute_comp_dslot K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ hτ hte1 (ht2D hτ) (ht3D hτ) z
  · refine (mem_rightSemilinear
      ((Γ.gaugeCast (topRoute_right_recast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom)).mpr ?_
    intro τ z
    exact gTopRoute_comp_right K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ τ (ht2R τ) z

end TopRoute

/-! ### `gBotRoute`'s `homGrading`, and its full membership

`gBotRoute = gq4Close ∘ GE5 ∘ GE4`'s `homGrading` is direct composition of
`GE4.mem_grading_univ`, `GE5.mem_grading_univ`, `GQ4Close.mem_grading_univ`
above (`gq4Close` itself is degree-`0`).  Bundling it with
`PentagonRouteEquiv.lean`'s five `K`-linear conditions with `t₄ ∈
gInterSpace Γ (a+b) c d e₄`, `t₅ ∈ gInterSpace Γ a b (c+d) e₅` needs two
composed `Γ.gaugeCast`s to collapse to the single cast `gQuadInterSpace`'s
own right-semilinearity condition is stated against — general helper
lemmas for `Γ.gaugeCast`'s composition, proved by `subst` along the
(fresh, universally quantified) index equalities. -/

section BotRoute

variable (e₄ : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
  x ∈ (Γ.D (a + b)).grading i →
  ∀ n : GBL Γ (a + b) c d,
    t₄ (x • n) = ((sgn (e₄ * i) : ℤˣ) : ℤ) • (x • t₄ n))
variable (e₅ : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
  z ∈ (Γ.D (c + d)).grading i →
  ∀ n : GBL Γ a b (c + d),
    t₅ (z • n) = ((sgn (e₅ * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- Two composed `Γ.gaugeCast`s along a chain `x = y = z` collapse to the
single cast along the transitivity — proved by `subst` along the (fresh,
universally quantified) index equalities. -/
private theorem gaugeCast_trans {x y z : G} (h1 : x = y) (h2 : y = z)
    (τ : (Γ.D x).carrier) :
    (Γ.gaugeCast h2).toAlgEquiv ((Γ.gaugeCast h1).toAlgEquiv τ)
      = (Γ.gaugeCast (h1.trans h2)).toAlgEquiv τ := by
  subst h1; subst h2; rfl

/-- `Γ.gaugeCast`'s inverse is the cast along the symmetric equality. -/
private theorem gaugeCast_symm_apply {x y : G} (h : x = y)
    (τ : (Γ.D y).carrier) :
    (Γ.gaugeCast h).toAlgEquiv.symm τ = (Γ.gaugeCast h.symm).toAlgEquiv τ := by
  subst h; rfl

/-- The `gBotRoute = gq4Close ∘ GE5 ∘ GE4` composite, unfolded. -/
private theorem gBotRoute_apply' (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      = gq4Close K Γ a b c d
          (GE5 K Γ a b c d e₅ t₅ ht₅ (GE4 K Γ a b c d e₄ t₄ ht₄ z)) := by
  show ((gq4Close K Γ a b c d).toLinearMap ∘ₗ GE5 K Γ a b c d e₅ t₅ ht₅
      ∘ₗ GE4 K Γ a b c d e₄ t₄ ht₄) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

/-- **`gBotRoute`'s `homGrading`**, degree `e₄ + e₅`. -/
theorem gBotRoute_mem_grading
    (ht4deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ (a + b) c d j',
      t₄ n ∈ GBR.grading Γ (a + b) c d (j' + e₄))
    (ht5deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ a b (c + d) j',
      t₅ n ∈ GBR.grading Γ a b (c + d) (j' + e₅))
    {i : ZMod 2} {z : GQ1 K Γ a b c d} (hz : z ∈ GQ1.grading K Γ a b c d i) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      ∈ GQ4.grading K Γ a b c d (i + (e₄ + e₅)) := by
  rw [gBotRoute_apply']
  have h1 := GE4.mem_grading_univ K Γ a b c d e₄ t₄ ht₄ ht4deg hz
  have h2 := GE5.mem_grading_univ K Γ a b c d e₅ t₅ ht₅ ht5deg h1
  have h3 := GQ4Close.mem_grading_univ K Γ a b c d h2
  rwa [show i + e₄ + e₅ = i + (e₄ + e₅) from by ring] at h3

private theorem botRoute_right_recast_eq4' : a + b + c + d = a + b + (c + d) := by
  rw [add_assoc]

private theorem botRoute_right_recast_eq5' : a + b + (c + d) = a + (b + (c + d)) := by
  rw [add_assoc]

private theorem botRoute_right_recast_eqF' : a + (b + c + d) = a + (b + (c + d)) :=
  congrArg (a + ·) (add_assoc b c d)

/-- The three composed `Γ.gaugeCast`s of `gBotRoute_comp_right` collapse to
the single cast `gQuadInterSpace`'s own right-semilinearity condition is
stated against. -/
private theorem botRoute_right_cast_eq' : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

private theorem botRoute_right_cast_apply' (τ : (Γ.D (a + b + c + d)).carrier) :
    (Γ.gaugeCast (botRoute_right_recast_eqF' a b c d)).toAlgEquiv.symm
        ((Γ.gaugeCast (botRoute_right_recast_eq5' a b c d)).toAlgEquiv
          ((Γ.gaugeCast (botRoute_right_recast_eq4' a b c d)).toAlgEquiv τ))
      = (Γ.gaugeCast (botRoute_right_cast_eq' a b c d)).toAlgEquiv τ := by
  rw [gaugeCast_symm_apply, gaugeCast_trans, gaugeCast_trans]

/-- **`gBotRoute` is a homogeneous degree-`(e₄ + e₅)` quadruple
intertwiner**, given `t₄ ∈ gInterSpace Γ (a+b) c d e₄`, `t₅ ∈ gInterSpace Γ
a b (c+d) e₅`. -/
theorem gBotRoute_mem
    (ht4 : t₄ ∈ gInterSpace K Γ (a + b) c d e₄)
    (ht5 : t₅ ∈ gInterSpace K Γ a b (c + d) e₅) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅
      ∈ gQuadInterSpace K Γ a b c d (e₄ + e₅) := by
  obtain ⟨hg4, -, heqB4, heqC4, hR4⟩ := (mem_gInterSpace_iff K Γ (a + b) c d).mp ht4
  obtain ⟨hg5, heqA5, heqB5, -, hR5⟩ := (mem_gInterSpace_iff K Γ a b (c + d)).mp ht5
  have ht4C := (mem_superEquivariant (Γ.D c).grading).mp heqB4
  have ht4D := (mem_superEquivariant (Γ.D d).grading).mp heqC4
  have ht4deg := (mem_homGrading (GBL.grading Γ (a + b) c d) (GBR.grading Γ (a + b) c d)).mp hg4
  have ht5A := (mem_superEquivariant (Γ.D a).grading).mp heqA5
  have ht5B := (mem_superEquivariant (Γ.D b).grading).mp heqB5
  have ht5deg := (mem_homGrading (GBL.grading Γ a b (c + d)) (GBR.grading Γ a b (c + d))).mp hg5
  have ht4R := (mem_rightSemilinear
    (Γ.gaugeCast (botRoute_right_recast_eq4' a b c d)).toAlgEquiv.toAlgHom.toRingHom).mp hR4
  have ht5R := (mem_rightSemilinear
    (Γ.gaugeCast (botRoute_right_recast_eq5' a b c d)).toAlgEquiv.toAlgHom.toRingHom).mp hR5
  refine (mem_gQuadInterSpace_iff K Γ a b c d).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (mem_homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d)).mpr ?_
    intro i z hz
    exact gBotRoute_mem_grading K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ ht4deg ht5deg hz
  · refine (mem_superEquivariant (Γ.D a).grading).mpr ?_
    intro k x hx z
    exact gBotRoute_comp_aslot K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hx (ht5A hx) z
  · refine (mem_superEquivariant (Γ.D b).grading).mpr ?_
    intro k y hy z
    exact gBotRoute_comp_bslot K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hy (ht5B hy) z
  · refine (mem_superEquivariant (Γ.D c).grading).mpr ?_
    intro k z0 hz0 z
    exact gBotRoute_comp_cslot K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hz0 (ht4C hz0) z
  · refine (mem_superEquivariant (Γ.D d).grading).mpr ?_
    intro k τ hτ z
    exact gBotRoute_comp_dslot K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ hτ (ht4D hτ) z
  · refine (mem_rightSemilinear
      ((Γ.gaugeCast (botRoute_right_cast_eq' a b c d)).toAlgEquiv.toAlgHom.toRingHom)).mpr ?_
    intro τ z
    have h := gBotRoute_comp_right K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ τ (ht4R τ)
      (fun n => ht5R ((Γ.gaugeCast (botRoute_right_recast_eq4' a b c d)).toAlgEquiv τ) n) z
    rwa [botRoute_right_cast_apply'] at h

end BotRoute

end GaugeChi

end Superfusion
