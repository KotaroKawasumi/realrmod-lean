/-
Superfusion / GaugeChi / PentagonRouteEquiv

Milestone M12-4 of the abstract `(p, χ)` arc (continued): **the
homogeneous-generator induction bridges at each pentagon vertex, and the
"generator-∀ → universal" upgrade of every edge's slot/right transport** —
the Γ-mirror of `Superfusion.Bimod.QuadMembership`.

The one reusable induction principle behind every upgrade
(`RelTensor.induction_on_left_homog`, `Bimod.PentagonB`) is *already
general* (over an arbitrary balanced tensor `M ⊗[A] N`), so it is reused
**verbatim** here, not rebuilt; only the *vertex-level* bridges
(`GBR.induction_on_left_homog`, `GQ2.induction_on_gen`, …) threading it
through each vertex's own synonym `mk` are transcribed, exactly mirroring
`QuadMembership.lean`'s own vertex layer.

Once every vertex carries its induction bridges, each edge's `comp_*`
(`GaugeChi.PentagonEdgeEquiv`, generator-∀) upgrades to a fully universal
`comp_*_univ` (∀ n : Vertex) by induction + `K`-linearity — `GE2`, `GE3`,
`GE4`, `GE5`, `GQ4Close` each get such a suite (`GE1`'s own transports are
already universal, via `Bimod.MapEquivariance`'s general `End`-descent).
Composing the now-universal edge laws for `GE1`–`GE3` (`gTopRoute`) resp.
`GE4`, `GE5`, `gq4Close` (`gBotRoute`) is then direct function composition
— `gTopRoute_comp_*`/`gBotRoute_comp_*`, at composite degrees
`e₁ + e₂ + e₃` resp. `e₄ + e₅`.

**Scope**: the five `K`-linear conditions (four slot super-equivariances +
right-semilinearity) for both routes, universal in the vertex argument.
The sixth condition (`homGrading`, needing a *degree-matching* induction)
and the final `∈ gQuadInterSpace` assembly continue in
`GaugeChi.PentagonRouteMembership`.
-/
import Superfusion.GaugeChi.PentagonMembership
import Superfusion.Bimod.QuadMembership2

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

/-! ### Vertex layer: two-level generator induction at `GQ2` -/

/-- Raw (unconditional) generator induction at `GBR`, through its own
`mk`. -/
@[elab_as_elim]
theorem GBR.induction_on {motive : GBR Γ a b c → Prop}
    (y : GBR Γ a b c)
    (zero : motive 0)
    (mk : ∀ (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c))),
      motive (GBR.mk Γ a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  RelTensor.induction_on K (Γ.D (b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (FusionColumn (Γ.fuse a (b + c))) y zero mk add

/-- Homogeneous-generator induction at `GBR`, through its own `mk`. -/
@[elab_as_elim]
theorem GBR.induction_on_left_homog {motive : GBR Γ a b c → Prop}
    (y : GBR Γ a b c)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c))),
      u ∈ FusionColumn.grading (Γ.fuse b c) j → motive (GBR.mk Γ a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse b c)) y zero homog add

/-- Raw (unconditional) generator induction at `GQ2`, through its own
`mk`. -/
@[elab_as_elim]
theorem GQ2.induction_on {motive : GQ2 K Γ a b c d → Prop}
    (z : GQ2 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (m : GBR Γ a b c) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      motive (GQ2.mk K Γ a b c d m w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (a + b + c)).carrier
    (GBR Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) z zero mk add

/-- **Two-level generator induction at `GQ2`**, `u` homogeneous. -/
@[elab_as_elim]
theorem GQ2.induction_on_gen {motive : GQ2 K Γ a b c d → Prop}
    (n : GQ2 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
      (w : FusionColumn (Γ.fuse (a + b + c) d)), u ∈ FusionColumn.grading (Γ.fuse b c) j →
      motive (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ2.induction_on K Γ a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using GBR.induction_on_left_homog K Γ a b c with
      | zero =>
          rw [show GQ2.mk K Γ a b c d (0 : GBR Γ a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog j u v hu => exact homog u v w hu
      | add y y' hy hy' =>
          rw [show GQ2.mk K Γ a b c d (y + y') w
              = GQ2.mk K Γ a b c d y w + GQ2.mk K Γ a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### Vertex layer: three-level generator induction at `GQ2` -/

/-- Homogeneous-generator induction at `GBR`, both factors. -/
@[elab_as_elim]
theorem GBR.induction_on_gen2 {motive : GBR Γ a b c → Prop}
    (y : GBR Γ a b c)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c))),
      u ∈ FusionColumn.grading (Γ.fuse b c) j → v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv →
      motive (GBR.mk Γ a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y := by
  induction y using GBR.induction_on_left_homog K Γ a b c with
  | zero => exact zero
  | homog j u n hu =>
      induction n using DirectSum.Decomposition.inductionOn
        (FusionColumn.grading (Γ.fuse a (b + c))) with
      | zero =>
          rw [show GBR.mk Γ a b c u (0 : FusionColumn (Γ.fuse a (b + c))) = 0 from by
            simp only [map_zero]]
          exact zero
      | add v v' hv hv' =>
          rw [show GBR.mk Γ a b c u (v + v') = GBR.mk Γ a b c u v + GBR.mk Γ a b c u v' from by
            simp only [map_add]]
          exact add _ _ hv hv'
      | homogeneous xv => exact homog u xv.1 hu xv.2
  | add y y' hy hy' => exact add y y' hy hy'

/-- **Three-level generator induction at `GQ2`**, `u`, `v` both
homogeneous. -/
@[elab_as_elim]
theorem GQ2.induction_on_gen2 {motive : GQ2 K Γ a b c d → Prop}
    (n : GQ2 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse a (b + c)))
      (w : FusionColumn (Γ.fuse (a + b + c) d)), u ∈ FusionColumn.grading (Γ.fuse b c) j →
      v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv →
      motive (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ2.induction_on K Γ a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using GBR.induction_on_gen2 K Γ a b c with
      | zero =>
          rw [show GQ2.mk K Γ a b c d (0 : GBR Γ a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog u v hu hv => exact homog u v w hu hv
      | add y y' hy hy' =>
          rw [show GQ2.mk K Γ a b c d (y + y') w
              = GQ2.mk K Γ a b c d y w + GQ2.mk K Γ a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### `GE2`'s slot and right transports, upgraded to universal -/

namespace GE2

variable (e : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
  y ∈ (Γ.D (b + c)).grading i →
  ∀ n : GQ2rInner K Γ a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- **`GE2`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {s : ℤ} {k : ZMod 2}
    {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht₂A : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w)
        = s • (x • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))
    (n : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d e t₂ ht₂ (x • n) = s • (x • GE2 K Γ a b c d e t₂ ht₂ n) := by
  induction n using GQ2.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_aslot K Γ a b c d e t₂ ht₂ hx ht₂A hu v w
  | add p q hp hq =>
      have h1 : GE2 K Γ a b c d e t₂ ht₂ (x • (p + q))
          = GE2 K Γ a b c d e t₂ ht₂ (x • p) + GE2 K Γ a b c d e t₂ ht₂ (x • q) := by
        rw [smul_add, map_add]
      have h2 : GE2 K Γ a b c d e t₂ ht₂ (p + q)
          = GE2 K Γ a b c d e t₂ ht₂ p + GE2 K Γ a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE2`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {i : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading i)
    (n : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d e t₂ ht₂ (y • n)
      = ((sgn (e * i) : ℤˣ) : ℤ) • (y • GE2 K Γ a b c d e t₂ ht₂ n) := by
  induction n using GQ2.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_bslot K Γ a b c d e t₂ ht₂ hy hu v w
  | add p q hp hq =>
      have h1 : GE2 K Γ a b c d e t₂ ht₂ (y • (p + q))
          = GE2 K Γ a b c d e t₂ ht₂ (y • p) + GE2 K Γ a b c d e t₂ ht₂ (y • q) := by
        rw [smul_add, map_add]
      have h2 : GE2 K Γ a b c d e t₂ ht₂ (p + q)
          = GE2 K Γ a b c d e t₂ ht₂ p + GE2 K Γ a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE2`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {i : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading i)
    (n : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d e t₂ ht₂ (z0 • n)
      = ((sgn (e * i) : ℤˣ) : ℤ) • (z0 • GE2 K Γ a b c d e t₂ ht₂ n) := by
  induction n using GQ2.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_cslot K Γ a b c d e t₂ ht₂ hz0 hu v w
  | add p q hp hq =>
      have h1 : GE2 K Γ a b c d e t₂ ht₂ (z0 • (p + q))
          = GE2 K Γ a b c d e t₂ ht₂ (z0 • p) + GE2 K Γ a b c d e t₂ ht₂ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : GE2 K Γ a b c d e t₂ ht₂ (p + q)
          = GE2 K Γ a b c d e t₂ ht₂ p + GE2 K Γ a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast of the total coefficient algebra used by
`comp_right_univ` (matches `PentagonEdgeEquiv.lean`'s private
`right_recast_eq`, re-proved here since `private` names do not cross
files). -/
private theorem right_recast_eq : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- **`GE2`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht₂R : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))
    (n : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d e t₂ ht₂ (MulOpposite.op τ • n)
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)
          • GE2 K Γ a b c d e t₂ ht₂ n := by
  induction n using GQ2.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_right K Γ a b c d e t₂ ht₂ τ ht₂R hu v w
  | add p q hp hq =>
      have h1 : GE2 K Γ a b c d e t₂ ht₂ (MulOpposite.op τ • (p + q))
          = GE2 K Γ a b c d e t₂ ht₂ (MulOpposite.op τ • p)
            + GE2 K Γ a b c d e t₂ ht₂ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE2 K Γ a b c d e t₂ ht₂ (p + q)
          = GE2 K Γ a b c d e t₂ ht₂ p + GE2 K Γ a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`GE2`'s `d`-slot transport, universal.**  Built on the *clean-form*
`comp_dslot'`. -/
theorem comp_dslot_univ {s' : ℤ} {m : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₂D' : ∀ x : GQ2rInner K Γ a b c d, t₂ (τ • x) = s' • (τ • t₂ x))
    (n : GQ2 K Γ a b c d) :
    GE2 K Γ a b c d e t₂ ht₂ (τ • n) = s' • (τ • GE2 K Γ a b c d e t₂ ht₂ n) := by
  induction n using GQ2.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot' K Γ a b c d e t₂ ht₂ hτ ht₂D' hu hv w
  | add p q hp hq =>
      have h1 : GE2 K Γ a b c d e t₂ ht₂ (τ • (p + q))
          = GE2 K Γ a b c d e t₂ ht₂ (τ • p) + GE2 K Γ a b c d e t₂ ht₂ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE2 K Γ a b c d e t₂ ht₂ (p + q)
          = GE2 K Γ a b c d e t₂ ht₂ p + GE2 K Γ a b c d e t₂ ht₂ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

end GE2

/-! ### Vertex layer: generator induction at `GQ3` -/

/-- Raw (unconditional) generator induction at `GQ3Inner`, through its own
spelling `GBR.mk Γ a (b+c) d`. -/
@[elab_as_elim]
theorem GQ3Inner.induction_on {motive : GQ3Inner K Γ a b c d → Prop}
    (x : GQ3Inner K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (v : FusionColumn (Γ.fuse (b + c) d)) (w : FusionColumn (Γ.fuse a (b + c + d))),
      motive (GBR.mk Γ a (b + c) d v w : GQ3Inner K Γ a b c d))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  RelTensor.induction_on K (Γ.D (b + c + d)).carrier
    (FusionColumn (Γ.fuse (b + c) d)) (FusionColumn (Γ.fuse a (b + c + d))) x zero mk add

/-- Homogeneous-generator induction at `GQ3Inner`, through its own
spelling `GBR.mk Γ a (b+c) d` (`v` homogeneous). -/
@[elab_as_elim]
theorem GQ3Inner.induction_on_left_homog {motive : GQ3Inner K Γ a b c d → Prop}
    (x : GQ3Inner K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ (i : ZMod 2) (v : FusionColumn (Γ.fuse (b + c) d))
      (w : FusionColumn (Γ.fuse a (b + c + d))),
      v ∈ FusionColumn.grading (Γ.fuse (b + c) d) i →
      motive (GBR.mk Γ a (b + c) d v w : GQ3Inner K Γ a b c d))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse (b + c) d)) x zero homog add

/-- Raw (unconditional) generator induction at `GQ3`, through its own
`mk`. -/
@[elab_as_elim]
theorem GQ3.induction_on {motive : GQ3 K Γ a b c d → Prop}
    (z : GQ3 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (u : FusionColumn (Γ.fuse b c)) (x : GQ3Inner K Γ a b c d),
      motive (GQ3.mk K Γ a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (b + c)).carrier
    (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) z zero mk add

/-- Homogeneous-generator induction at `GQ3`, through its own `mk`. -/
@[elab_as_elim]
theorem GQ3.induction_on_left_homog {motive : GQ3 K Γ a b c d → Prop}
    (z : GQ3 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : FusionColumn (Γ.fuse b c)) (x : GQ3Inner K Γ a b c d),
      u ∈ FusionColumn.grading (Γ.fuse b c) j → motive (GQ3.mk K Γ a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse b c)) z zero homog add

/-- **Two-level generator induction at `GQ3`, raw in `GQ3Inner`**: for the
`b`-, `c`-slots and the right action of `GE3`, none of which need any
homogeneity at all. -/
@[elab_as_elim]
theorem GQ3.induction_on_raw {motive : GQ3 K Γ a b c d → Prop}
    (n : GQ3 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
      (w : FusionColumn (Γ.fuse a (b + c + d))),
      motive (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ3.induction_on K Γ a b c d with
  | zero => exact zero
  | mk u x =>
      induction x using GQ3Inner.induction_on K Γ a b c d with
      | zero =>
          rw [show GQ3.mk K Γ a b c d u (0 : GQ3Inner K Γ a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk v w => exact mk u v w
      | add x x' hx hx' =>
          rw [show GQ3.mk K Γ a b c d u (x + x')
              = GQ3.mk K Γ a b c d u x + GQ3.mk K Γ a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Two-level generator induction at `GQ3`, `u` homogeneous**: for
`GE3`'s `d`-slot. -/
@[elab_as_elim]
theorem GQ3.induction_on_gen {motive : GQ3 K Γ a b c d → Prop}
    (n : GQ3 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
      (w : FusionColumn (Γ.fuse a (b + c + d))), u ∈ FusionColumn.grading (Γ.fuse b c) j →
      motive (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ3.induction_on_left_homog K Γ a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using GQ3Inner.induction_on K Γ a b c d with
      | zero =>
          rw [show GQ3.mk K Γ a b c d u (0 : GQ3Inner K Γ a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk v w => exact homog u v w hu
      | add x x' hx hx' =>
          rw [show GQ3.mk K Γ a b c d u (x + x')
              = GQ3.mk K Γ a b c d u x + GQ3.mk K Γ a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `GQ3`, `u`, `v` both
homogeneous**: for `GE3`'s `a`-slot. -/
@[elab_as_elim]
theorem GQ3.induction_on_gen2 {motive : GQ3 K Γ a b c d → Prop}
    (n : GQ3 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
      (w : FusionColumn (Γ.fuse a (b + c + d))), u ∈ FusionColumn.grading (Γ.fuse b c) j →
      v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv →
      motive (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ3.induction_on_left_homog K Γ a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using GQ3Inner.induction_on_left_homog K Γ a b c d with
      | zero =>
          rw [show GQ3.mk K Γ a b c d u (0 : GQ3Inner K Γ a b c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog jv v w hv => exact homog u v w hu hv
      | add x x' hx hx' =>
          rw [show GQ3.mk K Γ a b c d u (x + x')
              = GQ3.mk K Γ a b c d u x + GQ3.mk K Γ a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `GE3`'s slot and right transports, upgraded to universal -/

namespace GE3

variable (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
variable (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- **`GE3`'s `b`-slot transport, universal** — no homogeneity needed at
all, so the upgrade is a *raw* two-level induction. -/
theorem comp_bslot_univ {s : ℤ} {y : (Γ.D b).carrier}
    (ht₃B : ∀ m : GBL Γ b c d, t₃ (y • m) = s • (y • t₃ m))
    (n : GQ3 K Γ a b c d) :
    GE3 K Γ a b c d t₃ ht₃ (y • n) = s • (y • GE3 K Γ a b c d t₃ ht₃ n) := by
  induction n using GQ3.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_bslot K Γ a b c d t₃ ht₃ ht₃B u v w
  | add p q hp hq =>
      have h1 : GE3 K Γ a b c d t₃ ht₃ (y • (p + q))
          = GE3 K Γ a b c d t₃ ht₃ (y • p) + GE3 K Γ a b c d t₃ ht₃ (y • q) := by
        rw [smul_add, map_add]
      have h2 : GE3 K Γ a b c d t₃ ht₃ (p + q)
          = GE3 K Γ a b c d t₃ ht₃ p + GE3 K Γ a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE3`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {s : ℤ} {z0 : (Γ.D c).carrier}
    (ht₃C : ∀ m : GBL Γ b c d, t₃ (z0 • m) = s • (z0 • t₃ m))
    (n : GQ3 K Γ a b c d) :
    GE3 K Γ a b c d t₃ ht₃ (z0 • n) = s • (z0 • GE3 K Γ a b c d t₃ ht₃ n) := by
  induction n using GQ3.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_cslot K Γ a b c d t₃ ht₃ ht₃C u v w
  | add p q hp hq =>
      have h1 : GE3 K Γ a b c d t₃ ht₃ (z0 • (p + q))
          = GE3 K Γ a b c d t₃ ht₃ (z0 • p) + GE3 K Γ a b c d t₃ ht₃ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : GE3 K Γ a b c d t₃ ht₃ (p + q)
          = GE3 K Γ a b c d t₃ ht₃ p + GE3 K Γ a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE3`'s right-action transport, universal** — plain, no cast at
all. -/
theorem comp_right_univ (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (n : GQ3 K Γ a b c d) :
    GE3 K Γ a b c d t₃ ht₃ (τ • n) = τ • GE3 K Γ a b c d t₃ ht₃ n := by
  induction n using GQ3.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk u v w => exact comp_right K Γ a b c d t₃ ht₃ τ u v w
  | add p q hp hq =>
      have h1 : GE3 K Γ a b c d t₃ ht₃ (τ • (p + q))
          = GE3 K Γ a b c d t₃ ht₃ (τ • p) + GE3 K Γ a b c d t₃ ht₃ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE3 K Γ a b c d t₃ ht₃ (p + q)
          = GE3 K Γ a b c d t₃ ht₃ p + GE3 K Γ a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`GE3`'s `d`-slot transport, universal.** -/
theorem comp_dslot_univ {s : ℤ} {m : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₃D : ∀ n : GBL Γ b c d, t₃ (τ • n) = s • (τ • t₃ n))
    (n : GQ3 K Γ a b c d) :
    GE3 K Γ a b c d t₃ ht₃ (τ • n) = s • (τ • GE3 K Γ a b c d t₃ ht₃ n) := by
  induction n using GQ3.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_dslot K Γ a b c d t₃ ht₃ hτ ht₃D hu v w
  | add p q hp hq =>
      have h1 : GE3 K Γ a b c d t₃ ht₃ (τ • (p + q))
          = GE3 K Γ a b c d t₃ ht₃ (τ • p) + GE3 K Γ a b c d t₃ ht₃ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE3 K Γ a b c d t₃ ht₃ (p + q)
          = GE3 K Γ a b c d t₃ ht₃ p + GE3 K Γ a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE3`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {e k : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e))
    {x : (Γ.D a).carrier} (hx : x ∈ (Γ.D a).grading k)
    (n : GQ3 K Γ a b c d) :
    GE3 K Γ a b c d t₃ ht₃ (x • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (x • GE3 K Γ a b c d t₃ ht₃ n) := by
  induction n using GQ3.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_aslot K Γ a b c d t₃ ht₃ ht₃deg hx hu hv w
  | add p q hp hq =>
      have h1 : GE3 K Γ a b c d t₃ ht₃ (x • (p + q))
          = GE3 K Γ a b c d t₃ ht₃ (x • p) + GE3 K Γ a b c d t₃ ht₃ (x • q) := by
        rw [smul_add, map_add]
      have h2 : GE3 K Γ a b c d t₃ ht₃ (p + q)
          = GE3 K Γ a b c d t₃ ht₃ p + GE3 K Γ a b c d t₃ ht₃ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

end GE3

/-! ### `gTopRoute`'s slot and right transports

With `GE1` already universal (general `RelTensor.map` descent) and `GE2`,
`GE3` upgraded above, `gTopRoute = GE3 ∘ GE2 ∘ GE1`'s own transport laws are
now *direct function composition* — no further induction needed. -/

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

private theorem gTopRoute_apply (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z
      = GE3 K Γ a b c d t₃ ht₃
          (GE2 K Γ a b c d e₂ t₂ ht₂ (GE1 K Γ a b c d t₁ ht₁ z)) := by
  show (GE3 K Γ a b c d t₃ ht₃ ∘ₗ GE2 K Γ a b c d e₂ t₂ ht₂ ∘ₗ GE1 K Γ a b c d t₁ ht₁) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]

private theorem zmod2_topRoute_deg (e₁ e₂ e₃ k : ZMod 2) :
    e₁ * k + e₂ * k + e₃ * k = (e₁ + e₂ + e₃) * k := by ring

/-- The associativity recast used by `gTopRoute_comp_right`. -/
private theorem topRoute_right_recast_eq :
    a + b + c + d = a + (b + c + d) := by rw [add_assoc, add_assoc, add_assoc]

/-- **`gTopRoute`'s `a`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem gTopRoute_comp_aslot
    {e₁ e₃ k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht1A : ∀ m : GBL Γ a b c, t₁ (x • m) = ((sgn (e₁ * k) : ℤˣ) : ℤ) • (x • t₁ m))
    (ht2A : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w)
        = ((sgn (e₂ * k) : ℤˣ) : ℤ) •
            (x • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))
    (ht3deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e₃))
    (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (x • z)
      = ((sgn ((e₁ + e₂ + e₃) * k) : ℤˣ) : ℤ) •
          (x • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [gTopRoute_apply, gTopRoute_apply,
    GE1.comp_aslot K Γ a b c d t₁ ht₁ ht1A z, map_zsmul,
    GE2.comp_aslot_univ K Γ a b c d e₂ t₂ ht₂ hx ht2A, map_zsmul, map_zsmul,
    GE3.comp_aslot_univ K Γ a b c d t₃ ht₃ ht3deg hx, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`gTopRoute`'s `b`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem gTopRoute_comp_bslot
    {e₁ e₃ i : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading i)
    (ht1B : ∀ m : GBL Γ a b c, t₁ (y • m) = ((sgn (e₁ * i) : ℤˣ) : ℤ) • (y • t₁ m))
    (ht3B : ∀ m : GBL Γ b c d, t₃ (y • m) = ((sgn (e₃ * i) : ℤˣ) : ℤ) • (y • t₃ m))
    (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (y • z)
      = ((sgn ((e₁ + e₂ + e₃) * i) : ℤˣ) : ℤ) •
          (y • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [gTopRoute_apply, gTopRoute_apply,
    GE1.comp_bslot K Γ a b c d t₁ ht₁ ht1B z, map_zsmul,
    GE2.comp_bslot_univ K Γ a b c d e₂ t₂ ht₂ hy, map_zsmul, map_zsmul,
    GE3.comp_bslot_univ K Γ a b c d t₃ ht₃ ht3B, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`gTopRoute`'s `c`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem gTopRoute_comp_cslot
    {e₁ e₃ i : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading i)
    (ht1C : ∀ m : GBL Γ a b c, t₁ (z0 • m) = ((sgn (e₁ * i) : ℤˣ) : ℤ) • (z0 • t₁ m))
    (ht3C : ∀ m : GBL Γ b c d, t₃ (z0 • m) = ((sgn (e₃ * i) : ℤˣ) : ℤ) • (z0 • t₃ m))
    (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (z0 • z)
      = ((sgn ((e₁ + e₂ + e₃) * i) : ℤˣ) : ℤ) •
          (z0 • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [gTopRoute_apply, gTopRoute_apply,
    GE1.comp_cslot K Γ a b c d t₁ ht₁ ht1C z, map_zsmul,
    GE2.comp_cslot_univ K Γ a b c d e₂ t₂ ht₂ hz0, map_zsmul, map_zsmul,
    GE3.comp_cslot_univ K Γ a b c d t₃ ht₃ ht3C, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`gTopRoute`'s `d`-slot transport**, degree `e₁ + e₂ + e₃`. -/
theorem gTopRoute_comp_dslot
    {e₁ e₃ m : ZMod 2} {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (hte1 : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ a b c j',
      t₁ n ∈ GBR.grading Γ a b c (j' + e₁))
    (ht2D' : ∀ x : GQ2rInner K Γ a b c d,
      t₂ (τ • x) = ((sgn (e₂ * m) : ℤˣ) : ℤ) • (τ • t₂ x))
    (ht3D : ∀ n : GBL Γ b c d, t₃ (τ • n) = ((sgn (e₃ * m) : ℤˣ) : ℤ) • (τ • t₃ n))
    (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (τ • z)
      = ((sgn ((e₁ + e₂ + e₃) * m) : ℤˣ) : ℤ) •
          (τ • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z) := by
  rw [gTopRoute_apply, gTopRoute_apply,
    GE1.comp_dslot K Γ a b c d t₁ ht₁ hte1 hτ z, map_zsmul,
    GE2.comp_dslot_univ K Γ a b c d e₂ t₂ ht₂ hτ ht2D', map_zsmul, map_zsmul,
    GE3.comp_dslot_univ K Γ a b c d t₃ ht₃ hτ ht3D, smul_smul, smul_smul]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_topRoute_deg]

/-- **`gTopRoute`'s right-action transport**, along the associativity
recast `D_{((a+b)+c)+d} ≅ D_{a+((b+c)+d)}` (matching `gQuadInterSpace`'s
own `quadRightCast_eq`) — the *same* recast as `GE2`'s own `comp_right`
(`GE1`'s and `GE3`'s legs carry no cast at all). -/
theorem gTopRoute_comp_right
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht2R : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((Γ.gaugeCast (topRoute_right_recast_eq a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))
    (z : GQ1 K Γ a b c d) :
    gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ (MulOpposite.op τ • z)
      = MulOpposite.op ((Γ.gaugeCast
            (topRoute_right_recast_eq a b c d)).toAlgEquiv τ)
          • gTopRoute K Γ a b c d t₁ ht₁ e₂ t₂ ht₂ t₃ ht₃ z := by
  rw [gTopRoute_apply, gTopRoute_apply,
    GE1.comp_right K Γ a b c d t₁ ht₁ (MulOpposite.op τ) z,
    GE2.comp_right_univ K Γ a b c d e₂ t₂ ht₂ τ ht2R,
    GE3.comp_right_univ K Γ a b c d t₃ ht₃]

end TopRoute

/-! ### Vertex layer: generator induction at `GQ1` (mirrors `GQ2`, `GBL` in
place of `GBR`) -/

/-- Homogeneous-generator induction at `GBL`, through its own `mk`. -/
@[elab_as_elim]
theorem GBL.induction_on_left_homog {motive : GBL Γ a b c → Prop}
    (y : GBL Γ a b c)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c)),
      u ∈ FusionColumn.grading (Γ.fuse a b) j → motive (GBL.mk Γ a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse a b)) y zero homog add

/-- Homogeneous-generator induction at `GBL`, both factors. -/
@[elab_as_elim]
theorem GBL.induction_on_gen2 {motive : GBL Γ a b c → Prop}
    (y : GBL Γ a b c)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c)),
      u ∈ FusionColumn.grading (Γ.fuse a b) j → v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv →
      motive (GBL.mk Γ a b c u v))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive y := by
  induction y using GBL.induction_on_left_homog K Γ a b c with
  | zero => exact zero
  | homog j u n hu =>
      induction n using DirectSum.Decomposition.inductionOn
        (FusionColumn.grading (Γ.fuse (a + b) c)) with
      | zero =>
          rw [show GBL.mk Γ a b c u (0 : FusionColumn (Γ.fuse (a + b) c)) = 0 from by
            simp only [map_zero]]
          exact zero
      | add v v' hv hv' =>
          rw [show GBL.mk Γ a b c u (v + v') = GBL.mk Γ a b c u v + GBL.mk Γ a b c u v' from by
            simp only [map_add]]
          exact add _ _ hv hv'
      | homogeneous xv => exact homog u xv.1 hu xv.2
  | add y y' hy hy' => exact add y y' hy hy'

/-- Raw (unconditional) generator induction at `GQ1`, through its own
`mk`. -/
@[elab_as_elim]
theorem GQ1.induction_on {motive : GQ1 K Γ a b c d → Prop}
    (z : GQ1 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (m : GBL Γ a b c) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      motive (GQ1.mk K Γ a b c d m w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (a + b + c)).carrier
    (GBL Γ a b c) (FusionColumn (Γ.fuse (a + b + c) d)) z zero mk add

/-- **Two-level generator induction at `GQ1`**, `u` homogeneous. -/
@[elab_as_elim]
theorem GQ1.induction_on_gen {motive : GQ1 K Γ a b c d → Prop}
    (n : GQ1 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j : ZMod 2} (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
      (w : FusionColumn (Γ.fuse (a + b + c) d)), u ∈ FusionColumn.grading (Γ.fuse a b) j →
      motive (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ1.induction_on K Γ a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using GBL.induction_on_left_homog K Γ a b c with
      | zero =>
          rw [show GQ1.mk K Γ a b c d (0 : GBL Γ a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog j u v hu => exact homog u v w hu
      | add y y' hy hy' =>
          rw [show GQ1.mk K Γ a b c d (y + y') w
              = GQ1.mk K Γ a b c d y w + GQ1.mk K Γ a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `GQ1`**, `u`, `v` both
homogeneous — for `GE4`'s `d`-slot. -/
@[elab_as_elim]
theorem GQ1.induction_on_gen2 {motive : GQ1 K Γ a b c d → Prop}
    (n : GQ1 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse (a + b) c))
      (w : FusionColumn (Γ.fuse (a + b + c) d)), u ∈ FusionColumn.grading (Γ.fuse a b) j →
      v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv →
      motive (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ1.induction_on K Γ a b c d with
  | zero => exact zero
  | mk y w =>
      induction y using GBL.induction_on_gen2 K Γ a b c with
      | zero =>
          rw [show GQ1.mk K Γ a b c d (0 : GBL Γ a b c) w = 0 from by
            simp only [map_zero, LinearMap.zero_apply]]
          exact zero
      | homog u v hu hv => exact homog u v w hu hv
      | add y y' hy hy' =>
          rw [show GQ1.mk K Γ a b c d (y + y') w
              = GQ1.mk K Γ a b c d y w + GQ1.mk K Γ a b c d y' w from by
            simp only [map_add, LinearMap.add_apply]]
          exact add _ _ hy hy'
  | add x y hx hy => exact add x y hx hy

/-! ### `GE4`'s slot and right transports, upgraded to universal -/

namespace GE4

variable (e : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
  x ∈ (Γ.D (a + b)).grading i →
  ∀ n : GBL Γ (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- **`GE4`'s `a`-slot transport, universal** — the *spectator* slot, no
extra hypothesis on `t₄`. -/
theorem comp_aslot_univ {k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (n : GQ1 K Γ a b c d) :
    GE4 K Γ a b c d e t₄ ht₄ (x • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (x • GE4 K Γ a b c d e t₄ ht₄ n) := by
  induction n using GQ1.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_aslot K Γ a b c d e t₄ ht₄ hx hu v w
  | add p q hp hq =>
      have h1 : GE4 K Γ a b c d e t₄ ht₄ (x • (p + q))
          = GE4 K Γ a b c d e t₄ ht₄ (x • p) + GE4 K Γ a b c d e t₄ ht₄ (x • q) := by
        rw [smul_add, map_add]
      have h2 : GE4 K Γ a b c d e t₄ ht₄ (p + q)
          = GE4 K Γ a b c d e t₄ ht₄ p + GE4 K Γ a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE4`'s `b`-slot transport, universal** — the *spectator* slot. -/
theorem comp_bslot_univ {k : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    (n : GQ1 K Γ a b c d) :
    GE4 K Γ a b c d e t₄ ht₄ (y • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (y • GE4 K Γ a b c d e t₄ ht₄ n) := by
  induction n using GQ1.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_bslot K Γ a b c d e t₄ ht₄ hy hu v w
  | add p q hp hq =>
      have h1 : GE4 K Γ a b c d e t₄ ht₄ (y • (p + q))
          = GE4 K Γ a b c d e t₄ ht₄ (y • p) + GE4 K Γ a b c d e t₄ ht₄ (y • q) := by
        rw [smul_add, map_add]
      have h2 : GE4 K Γ a b c d e t₄ ht₄ (p + q)
          = GE4 K Γ a b c d e t₄ ht₄ p + GE4 K Γ a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE4`'s `c`-slot transport, universal.** -/
theorem comp_cslot_univ {s : ℤ} {k : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading k)
    (ht₄C : ∀ n : GBL Γ (a + b) c d, t₄ (z0 • n) = s • (z0 • t₄ n))
    (n : GQ1 K Γ a b c d) :
    GE4 K Γ a b c d e t₄ ht₄ (z0 • n) = s • (z0 • GE4 K Γ a b c d e t₄ ht₄ n) := by
  induction n using GQ1.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_cslot K Γ a b c d e t₄ ht₄ hz0 ht₄C hu v w
  | add p q hp hq =>
      have h1 : GE4 K Γ a b c d e t₄ ht₄ (z0 • (p + q))
          = GE4 K Γ a b c d e t₄ ht₄ (z0 • p) + GE4 K Γ a b c d e t₄ ht₄ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : GE4 K Γ a b c d e t₄ ht₄ (p + q)
          = GE4 K Γ a b c d e t₄ ht₄ p + GE4 K Γ a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE4`'s `d`-slot transport, universal.** -/
theorem comp_dslot_univ {s' : ℤ} {m : ZMod 2} {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₄D : ∀ n : GBL Γ (a + b) c d, t₄ (τ • n) = s' • (τ • t₄ n))
    (n : GQ1 K Γ a b c d) :
    GE4 K Γ a b c d e t₄ ht₄ (τ • n) = s' • (τ • GE4 K Γ a b c d e t₄ ht₄ n) := by
  induction n using GQ1.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot K Γ a b c d e t₄ ht₄ hτ ht₄D hu hv w
  | add p q hp hq =>
      have h1 : GE4 K Γ a b c d e t₄ ht₄ (τ • (p + q))
          = GE4 K Γ a b c d e t₄ ht₄ (τ • p) + GE4 K Γ a b c d e t₄ ht₄ (τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE4 K Γ a b c d e t₄ ht₄ (p + q)
          = GE4 K Γ a b c d e t₄ ht₄ p + GE4 K Γ a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast used by `comp_right_univ`. -/
private theorem right_recast_eq4 : a + b + c + d = a + b + (c + d) := by
  rw [add_assoc]

/-- **`GE4`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht₄R : ∀ n : GBL Γ (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ) • t₄ n)
    (n : GQ1 K Γ a b c d) :
    GE4 K Γ a b c d e t₄ ht₄ (MulOpposite.op τ • n)
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ)
          • GE4 K Γ a b c d e t₄ ht₄ n := by
  induction n using GQ1.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu => exact comp_right K Γ a b c d e t₄ ht₄ τ ht₄R hu v w
  | add p q hp hq =>
      have h1 : GE4 K Γ a b c d e t₄ ht₄ (MulOpposite.op τ • (p + q))
          = GE4 K Γ a b c d e t₄ ht₄ (MulOpposite.op τ • p)
            + GE4 K Γ a b c d e t₄ ht₄ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE4 K Γ a b c d e t₄ ht₄ (p + q)
          = GE4 K Γ a b c d e t₄ ht₄ p + GE4 K Γ a b c d e t₄ ht₄ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end GE4

/-! ### Vertex layer: generator induction at `GQ5`

`GQ5 = C_{a,b} ⊗_{D_{a+b}} GBR(a{+}b,c,d)` — the same shape as `GQ3`,
directly (`GQ5`'s second factor is literally `GBR Γ (a+b) c d`). -/

/-- Raw (unconditional) generator induction at `GQ5`, through its own
`mk`. -/
@[elab_as_elim]
theorem GQ5.induction_on {motive : GQ5 K Γ a b c d → Prop}
    (z : GQ5 K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (u : FusionColumn (Γ.fuse a b)) (x : GBR Γ (a + b) c d),
      motive (GQ5.mk K Γ a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (a + b)).carrier
    (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) z zero mk add

/-- Homogeneous-generator induction at `GQ5`, through its own `mk`. -/
@[elab_as_elim]
theorem GQ5.induction_on_left_homog {motive : GQ5 K Γ a b c d → Prop}
    (z : GQ5 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ (j : ZMod 2) (u : FusionColumn (Γ.fuse a b)) (x : GBR Γ (a + b) c d),
      u ∈ FusionColumn.grading (Γ.fuse a b) j → motive (GQ5.mk K Γ a b c d u x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse a b)) z zero homog add

/-- **Three-level generator induction at `GQ5`**, `u`, `v` both
homogeneous — every `GE5` condition needs both. -/
@[elab_as_elim]
theorem GQ5.induction_on_gen2 {motive : GQ5 K Γ a b c d → Prop}
    (n : GQ5 K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {j jv : ZMod 2} (u : FusionColumn (Γ.fuse a b)) (v : FusionColumn (Γ.fuse c d))
      (w : FusionColumn (Γ.fuse (a + b) (c + d))), u ∈ FusionColumn.grading (Γ.fuse a b) j →
      v ∈ FusionColumn.grading (Γ.fuse c d) jv →
      motive (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ5.induction_on_left_homog K Γ a b c d with
  | zero => exact zero
  | homog j u x hu =>
      induction x using GBR.induction_on_left_homog K Γ (a + b) c d with
      | zero =>
          rw [show GQ5.mk K Γ a b c d u (0 : GBR Γ (a + b) c d) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog jv v w hv => exact homog u v w hu hv
      | add x x' hx hx' =>
          rw [show GQ5.mk K Γ a b c d u (x + x')
              = GQ5.mk K Γ a b c d u x + GQ5.mk K Γ a b c d u x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `GE5`'s slot and right transports, upgraded to universal -/

namespace GE5

variable (e : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
  z ∈ (Γ.D (c + d)).grading i →
  ∀ n : GBL Γ a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- **`GE5`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {s : ℤ} {k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht₅A : ∀ n : GBL Γ a b (c + d), t₅ (x • n) = s • (x • t₅ n))
    (n : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d e t₅ ht₅ (x • n) = s • (x • GE5 K Γ a b c d e t₅ ht₅ n) := by
  induction n using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_aslot K Γ a b c d e t₅ ht₅ hx ht₅A hv hu w
  | add p q hp hq =>
      have h1 : GE5 K Γ a b c d e t₅ ht₅ (x • (p + q))
          = GE5 K Γ a b c d e t₅ ht₅ (x • p) + GE5 K Γ a b c d e t₅ ht₅ (x • q) := by
        rw [smul_add, map_add]
      have h2 : GE5 K Γ a b c d e t₅ ht₅ (p + q)
          = GE5 K Γ a b c d e t₅ ht₅ p + GE5 K Γ a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE5`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {s : ℤ} {k : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    (ht₅B : ∀ n : GBL Γ a b (c + d), t₅ (y • n) = s • (y • t₅ n))
    (n : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d e t₅ ht₅ (y • n) = s • (y • GE5 K Γ a b c d e t₅ ht₅ n) := by
  induction n using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_bslot K Γ a b c d e t₅ ht₅ hy ht₅B hv hu w
  | add p q hp hq =>
      have h1 : GE5 K Γ a b c d e t₅ ht₅ (y • (p + q))
          = GE5 K Γ a b c d e t₅ ht₅ (y • p) + GE5 K Γ a b c d e t₅ ht₅ (y • q) := by
        rw [smul_add, map_add]
      have h2 : GE5 K Γ a b c d e t₅ ht₅ (p + q)
          = GE5 K Γ a b c d e t₅ ht₅ p + GE5 K Γ a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE5`'s `c`-slot transport, universal** — the *spectator* slot. -/
theorem comp_cslot_univ {k : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading k)
    (n : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d e t₅ ht₅ (z0 • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (z0 • GE5 K Γ a b c d e t₅ ht₅ n) := by
  induction n using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_cslot K Γ a b c d e t₅ ht₅ hz0 hv hu w
  | add p q hp hq =>
      have h1 : GE5 K Γ a b c d e t₅ ht₅ (z0 • (p + q))
          = GE5 K Γ a b c d e t₅ ht₅ (z0 • p) + GE5 K Γ a b c d e t₅ ht₅ (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : GE5 K Γ a b c d e t₅ ht₅ (p + q)
          = GE5 K Γ a b c d e t₅ ht₅ p + GE5 K Γ a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- **`GE5`'s `d`-slot transport, universal** — the *spectator* slot. -/
theorem comp_dslot_univ {k : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k)
    (n : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d e t₅ ht₅ (t • n)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (t • GE5 K Γ a b c d e t₅ ht₅ n) := by
  induction n using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_dslot K Γ a b c d e t₅ ht₅ ht hv hu w
  | add p q hp hq =>
      have h1 : GE5 K Γ a b c d e t₅ ht₅ (t • (p + q))
          = GE5 K Γ a b c d e t₅ ht₅ (t • p) + GE5 K Γ a b c d e t₅ ht₅ (t • q) := by
        rw [smul_add, map_add]
      have h2 : GE5 K Γ a b c d e t₅ ht₅ (p + q)
          = GE5 K Γ a b c d e t₅ ht₅ p + GE5 K Γ a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add, smul_add]

/-- The associativity recast used by `comp_right_univ`. -/
private theorem right_recast_eq5' : a + b + (c + d) = a + (b + (c + d)) := by rw [add_assoc]

/-- **`GE5`'s right-action transport, universal.** -/
theorem comp_right_univ
    (τ : (Γ.D (a + b + (c + d))).carrier)
    (ht₅R : ∀ n : GBL Γ a b (c + d),
      t₅ (MulOpposite.op τ • n)
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq5' a b c d)).toAlgEquiv τ) • t₅ n)
    (n : GQ5 K Γ a b c d) :
    GE5 K Γ a b c d e t₅ ht₅ (MulOpposite.op τ • n)
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq5' a b c d)).toAlgEquiv τ)
          • GE5 K Γ a b c d e t₅ ht₅ n := by
  induction n using GQ5.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog u v w hu hv => exact comp_right K Γ a b c d e t₅ ht₅ τ ht₅R hv hu w
  | add p q hp hq =>
      have h1 : GE5 K Γ a b c d e t₅ ht₅ (MulOpposite.op τ • (p + q))
          = GE5 K Γ a b c d e t₅ ht₅ (MulOpposite.op τ • p)
            + GE5 K Γ a b c d e t₅ ht₅ (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : GE5 K Γ a b c d e t₅ ht₅ (p + q)
          = GE5 K Γ a b c d e t₅ ht₅ p + GE5 K Γ a b c d e t₅ ht₅ q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end GE5

/-! ### Vertex layer: generator induction at `GQ4r`

`GQ4r = C_{c,d} ⊗_{D_{c+d}} GBR(a,b,c{+}d)` — the same shape as `GQ3`,
`GQ5`. -/

/-- Raw (unconditional) generator induction at `GQ4r`, through its own
`mk`. -/
@[elab_as_elim]
theorem GQ4r.induction_on {motive : GQ4r K Γ a b c d → Prop}
    (z : GQ4r K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (v : FusionColumn (Γ.fuse c d)) (x : GBR Γ a b (c + d)),
      motive (GQ4r.mk K Γ a b c d v x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  RelTensor.induction_on K (Γ.D (c + d)).carrier
    (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) z zero mk add

/-- Homogeneous-generator induction at `GQ4r`, through its own `mk`. -/
@[elab_as_elim]
theorem GQ4r.induction_on_left_homog {motive : GQ4r K Γ a b c d → Prop}
    (z : GQ4r K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ (i : ZMod 2) (v : FusionColumn (Γ.fuse c d)) (x : GBR Γ a b (c + d)),
      v ∈ FusionColumn.grading (Γ.fuse c d) i → motive (GQ4r.mk K Γ a b c d v x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive z :=
  PentagonB.RelTensor.induction_on_left_homog K (FusionColumn.grading (Γ.fuse c d)) z zero homog add

/-- **Two-level generator induction at `GQ4r`, raw in the `GBR`
factor**: for `comp_cslot`, `comp_dslot`, `comp_right`, none of which need
any homogeneity at all. -/
@[elab_as_elim]
theorem GQ4r.induction_on_raw {motive : GQ4r K Γ a b c d → Prop}
    (n : GQ4r K Γ a b c d)
    (zero : motive 0)
    (mk : ∀ (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
      (w : FusionColumn (Γ.fuse a (b + (c + d)))),
      motive (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ4r.induction_on K Γ a b c d with
  | zero => exact zero
  | mk v x =>
      induction x using GBR.induction_on K Γ a b (c + d) with
      | zero =>
          rw [show GQ4r.mk K Γ a b c d v (0 : GBR Γ a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk u w => exact mk v u w
      | add x x' hx hx' =>
          rw [show GQ4r.mk K Γ a b c d v (x + x')
              = GQ4r.mk K Γ a b c d v x + GQ4r.mk K Γ a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Two-level generator induction at `GQ4r`, `v` homogeneous**: for
`comp_bslot`. -/
@[elab_as_elim]
theorem GQ4r.induction_on_gen {motive : GQ4r K Γ a b c d → Prop}
    (n : GQ4r K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {i : ZMod 2} (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
      (w : FusionColumn (Γ.fuse a (b + (c + d)))), v ∈ FusionColumn.grading (Γ.fuse c d) i →
      motive (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ4r.induction_on_left_homog K Γ a b c d with
  | zero => exact zero
  | homog i v x hv =>
      induction x using GBR.induction_on K Γ a b (c + d) with
      | zero =>
          rw [show GQ4r.mk K Γ a b c d v (0 : GBR Γ a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | mk u w => exact homog v u w hv
      | add x x' hx hx' =>
          rw [show GQ4r.mk K Γ a b c d v (x + x')
              = GQ4r.mk K Γ a b c d v x + GQ4r.mk K Γ a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-- **Three-level generator induction at `GQ4r`, `v`, `u` both
homogeneous**: for `comp_aslot`. -/
@[elab_as_elim]
theorem GQ4r.induction_on_gen2 {motive : GQ4r K Γ a b c d → Prop}
    (n : GQ4r K Γ a b c d)
    (zero : motive 0)
    (homog : ∀ {i j : ZMod 2} (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
      (w : FusionColumn (Γ.fuse a (b + (c + d)))), v ∈ FusionColumn.grading (Γ.fuse c d) i →
      u ∈ FusionColumn.grading (Γ.fuse b (c + d)) j →
      motive (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)))
    (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive n := by
  induction n using GQ4r.induction_on_left_homog K Γ a b c d with
  | zero => exact zero
  | homog i v x hv =>
      induction x using GBR.induction_on_left_homog K Γ a b (c + d) with
      | zero =>
          rw [show GQ4r.mk K Γ a b c d v (0 : GBR Γ a b (c + d)) = 0 from by
            simp only [map_zero]]
          exact zero
      | homog j u w hu => exact homog v u w hv hu
      | add x x' hx hx' =>
          rw [show GQ4r.mk K Γ a b c d v (x + x')
              = GQ4r.mk K Γ a b c d v x + GQ4r.mk K Γ a b c d v x' from by
            simp only [map_add]]
          exact add _ _ hx hx'
  | add x y hx hy => exact add x y hx hy

/-! ### `gq4Close`'s slot and right transports, upgraded to universal -/

namespace GQ4Close

/-- **`gq4Close`'s `a`-slot transport, universal.** -/
theorem comp_aslot_univ {k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (n : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d (x • n) = x • gq4Close K Γ a b c d n := by
  induction n using GQ4r.induction_on_gen2 K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog v u w hv hu => exact comp_aslot K Γ a b c d hv hu hx w
  | add p q hp hq =>
      have h1 : gq4Close K Γ a b c d (x • (p + q))
          = gq4Close K Γ a b c d (x • p) + gq4Close K Γ a b c d (x • q) := by
        rw [smul_add, map_add]
      have h2 : gq4Close K Γ a b c d (p + q)
          = gq4Close K Γ a b c d p + gq4Close K Γ a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`gq4Close`'s `b`-slot transport, universal.** -/
theorem comp_bslot_univ {i : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading i)
    (n : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d (y • n) = y • gq4Close K Γ a b c d n := by
  induction n using GQ4r.induction_on_gen K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | homog v u w hv => exact comp_bslot K Γ a b c d hv hy u w
  | add p q hp hq =>
      have h1 : gq4Close K Γ a b c d (y • (p + q))
          = gq4Close K Γ a b c d (y • p) + gq4Close K Γ a b c d (y • q) := by
        rw [smul_add, map_add]
      have h2 : gq4Close K Γ a b c d (p + q)
          = gq4Close K Γ a b c d p + gq4Close K Γ a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`gq4Close`'s `c`-slot transport, universal** — fully direct, no
homogeneity anywhere. -/
theorem comp_cslot_univ (z0 : (Γ.D c).carrier) (n : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d (z0 • n) = z0 • gq4Close K Γ a b c d n := by
  induction n using GQ4r.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_cslot K Γ a b c d v u w z0
  | add p q hp hq =>
      have h1 : gq4Close K Γ a b c d (z0 • (p + q))
          = gq4Close K Γ a b c d (z0 • p) + gq4Close K Γ a b c d (z0 • q) := by
        rw [smul_add, map_add]
      have h2 : gq4Close K Γ a b c d (p + q)
          = gq4Close K Γ a b c d p + gq4Close K Γ a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`gq4Close`'s `d`-slot transport, universal.** -/
theorem comp_dslot_univ (t : (Γ.D d).carrier) (n : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d (t • n) = t • gq4Close K Γ a b c d n := by
  induction n using GQ4r.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_dslot K Γ a b c d v u w t
  | add p q hp hq =>
      have h1 : gq4Close K Γ a b c d (t • (p + q))
          = gq4Close K Γ a b c d (t • p) + gq4Close K Γ a b c d (t • q) := by
        rw [smul_add, map_add]
      have h2 : gq4Close K Γ a b c d (p + q)
          = gq4Close K Γ a b c d p + gq4Close K Γ a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

/-- **`gq4Close`'s right-action transport, universal.** -/
theorem comp_right_univ (τ : (Γ.D (a + (b + (c + d)))).carrier)
    (n : GQ4r K Γ a b c d) :
    gq4Close K Γ a b c d (MulOpposite.op τ • n)
      = MulOpposite.op ((Γ.gaugeCast (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm τ)
          • gq4Close K Γ a b c d n := by
  induction n using GQ4r.induction_on_raw K Γ a b c d with
  | zero => simp only [smul_zero, map_zero]
  | mk v u w => exact comp_right K Γ a b c d v u w τ
  | add p q hp hq =>
      have h1 : gq4Close K Γ a b c d (MulOpposite.op τ • (p + q))
          = gq4Close K Γ a b c d (MulOpposite.op τ • p)
            + gq4Close K Γ a b c d (MulOpposite.op τ • q) := by
        rw [smul_add, map_add]
      have h2 : gq4Close K Γ a b c d (p + q)
          = gq4Close K Γ a b c d p + gq4Close K Γ a b c d q := map_add _ _ _
      rw [h1, hp, hq, h2, smul_add]

end GQ4Close

/-! ### `gBotRoute`'s slot and right transports

With `GE4`, `GE5`, `gq4Close` all upgraded above, `gBotRoute = gq4Close ∘
GE5 ∘ GE4`'s own transport laws are again direct function composition.
Unlike `gTopRoute`, `t₄`'s and `t₅`'s degrees `e₄`, `e₅` are already part of
`gBotRoute`'s own argument bundle; the composite degree is `e_bot = e₄ +
e₅` (`gq4Close` itself is degree-`0`). -/

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

private theorem gBotRoute_apply (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z
      = gq4Close K Γ a b c d
          (GE5 K Γ a b c d e₅ t₅ ht₅ (GE4 K Γ a b c d e₄ t₄ ht₄ z)) := by
  show ((gq4Close K Γ a b c d).toLinearMap ∘ₗ GE5 K Γ a b c d e₅ t₅ ht₅
      ∘ₗ GE4 K Γ a b c d e₄ t₄ ht₄) z = _
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rfl

private theorem zmod2_botRoute_deg (e₄ e₅ k : ZMod 2) :
    e₄ * k + e₅ * k = (e₄ + e₅) * k := by ring

private theorem botRoute_right_recast_eq4 : a + b + c + d = a + b + (c + d) := by
  rw [add_assoc]

private theorem botRoute_right_recast_eq5 : a + b + (c + d) = a + (b + (c + d)) := by
  rw [add_assoc]

/-- **`gBotRoute`'s `a`-slot transport**, degree `e₄ + e₅`. -/
theorem gBotRoute_comp_aslot
    {k : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht5A : ∀ n : GBL Γ a b (c + d), t₅ (x • n) = ((sgn (e₅ * k) : ℤˣ) : ℤ) • (x • t₅ n))
    (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (x • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (x • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [gBotRoute_apply, gBotRoute_apply,
    GE4.comp_aslot_univ K Γ a b c d e₄ t₄ ht₄ hx, map_zsmul,
    GE5.comp_aslot_univ K Γ a b c d e₅ t₅ ht₅ hx ht5A, map_zsmul, map_zsmul,
    GQ4Close.comp_aslot_univ K Γ a b c d hx, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`gBotRoute`'s `b`-slot transport**, degree `e₄ + e₅`. -/
theorem gBotRoute_comp_bslot
    {k : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    (ht5B : ∀ n : GBL Γ a b (c + d), t₅ (y • n) = ((sgn (e₅ * k) : ℤˣ) : ℤ) • (y • t₅ n))
    (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (y • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (y • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [gBotRoute_apply, gBotRoute_apply,
    GE4.comp_bslot_univ K Γ a b c d e₄ t₄ ht₄ hy, map_zsmul,
    GE5.comp_bslot_univ K Γ a b c d e₅ t₅ ht₅ hy ht5B, map_zsmul, map_zsmul,
    GQ4Close.comp_bslot_univ K Γ a b c d hy, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`gBotRoute`'s `c`-slot transport**, degree `e₄ + e₅`. -/
theorem gBotRoute_comp_cslot
    {k : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading k)
    (ht4C : ∀ n : GBL Γ (a + b) c d, t₄ (z0 • n) = ((sgn (e₄ * k) : ℤˣ) : ℤ) • (z0 • t₄ n))
    (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (z0 • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (z0 • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [gBotRoute_apply, gBotRoute_apply,
    GE4.comp_cslot_univ K Γ a b c d e₄ t₄ ht₄ hz0 ht4C, map_zsmul,
    GE5.comp_cslot_univ K Γ a b c d e₅ t₅ ht₅ hz0, map_zsmul, map_zsmul,
    GQ4Close.comp_cslot_univ K Γ a b c d, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`gBotRoute`'s `d`-slot transport**, degree `e₄ + e₅`. -/
theorem gBotRoute_comp_dslot
    {k : ZMod 2} {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading k)
    (ht4D : ∀ n : GBL Γ (a + b) c d, t₄ (τ • n) = ((sgn (e₄ * k) : ℤˣ) : ℤ) • (τ • t₄ n))
    (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (τ • z)
      = ((sgn ((e₄ + e₅) * k) : ℤˣ) : ℤ) •
          (τ • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z) := by
  rw [gBotRoute_apply, gBotRoute_apply,
    GE4.comp_dslot_univ K Γ a b c d e₄ t₄ ht₄ hτ ht4D, map_zsmul,
    GE5.comp_dslot_univ K Γ a b c d e₅ t₅ ht₅ hτ, map_zsmul, map_zsmul,
    GQ4Close.comp_dslot_univ K Γ a b c d, smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add, zmod2_botRoute_deg]

/-- **`gBotRoute`'s right-action transport**, along the composite
associativity recast threading through `GE4`'s, `GE5`'s and `gq4Close`'s
own casts. -/
theorem gBotRoute_comp_right
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht4R : ∀ n : GBL Γ (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((Γ.gaugeCast (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) • t₄ n)
    (ht5R : ∀ n : GBL Γ a b (c + d),
      t₅ (MulOpposite.op
            ((Γ.gaugeCast (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) • n)
        = MulOpposite.op ((Γ.gaugeCast (botRoute_right_recast_eq5 a b c d)).toAlgEquiv
              ((Γ.gaugeCast (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ)) • t₅ n)
    (z : GQ1 K Γ a b c d) :
    gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ (MulOpposite.op τ • z)
      = MulOpposite.op ((Γ.gaugeCast
            (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm
            ((Γ.gaugeCast (botRoute_right_recast_eq5 a b c d)).toAlgEquiv
              ((Γ.gaugeCast (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ)))
          • gBotRoute K Γ a b c d e₄ t₄ ht₄ e₅ t₅ ht₅ z := by
  rw [gBotRoute_apply, gBotRoute_apply,
    GE4.comp_right_univ K Γ a b c d e₄ t₄ ht₄ τ ht4R,
    GE5.comp_right_univ K Γ a b c d e₅ t₅ ht₅
      ((Γ.gaugeCast (botRoute_right_recast_eq4 a b c d)).toAlgEquiv τ) ht5R,
    GQ4Close.comp_right_univ K Γ a b c d]

end BotRoute

end GaugeChi

end Superfusion
