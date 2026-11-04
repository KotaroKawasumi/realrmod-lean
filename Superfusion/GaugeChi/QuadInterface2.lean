/-
Superfusion / GaugeChi / QuadInterface2

Milestone M12-8 of the abstract `(p, χ)` arc: **completing the quadruple
interface** — `mem_gQuadInterSpace_iff_gradedHomF`, the Γ-mirror of
`Superfusion.Bimod.QuadInterface2`, one gtensor level up from
`GaugeChi.GaugeParity`'s `mem_gInterSpace_iff_gradedHomF`.

`GQ4.aEmbed_smul`–`dEmbed_smul` (`QuadEnvModule2.lean`, this round) are
stated at the BUNDLED `.gtensor.carrier` spelling (unlike `Bimod`'s `Q4`,
whose `quadSource` gives a dedicated bundled type; here the bundled bridges
below, `GQ4_aEmbed_bundled`–`_dEmbed_bundled`, are `rfl`-transports of
those same theorems, needed because the `⊆` direction's `AlgHom`-mediated
route (`ιAB`/`ιABC`/`ιABCD`, `superEquivariantAt_of_includeLeft_includeRight`)
produces its slot generators through EXPLICIT `includeLeft`/`includeRight`
compositions rather than the single collapsed `hx₂`/`hy₂`/`hw₁`/`ht₀`
equations `aEmbed_smul`–`dEmbed_smul` themselves are stated against.  The
sixth condition (`rightSemilinear`) reuses `Bimod.QuadInterface2`'s general
right-sign reconciliation (`rightActionHom_equivariant_iff_rightSemilinear`)
verbatim, exactly as `GaugeChi.GaugeParity`'s triple-level
`rightSemilinear_of_gEnv` already does.
-/
import Superfusion.GaugeChi.QuadInterface

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

/-! ### `GQ4`'s bundled slot-embedding bridges -/

namespace GQ4

private theorem aEmbed_bundled
    (x₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading x₀)
    (x₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hx₂ : x₂ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading x₁)
    (z : GQ4 K Γ a b c d) :
    x₂ • z = x • z := by
  have hcol : x₂ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) := by
    rw [hx₂, hx₁, hx₀]; rfl
  rw [hcol]
  exact GQ4.aEmbed_smul K Γ a b c d _ x rfl _ rfl _ rfl z

private theorem bEmbed_bundled
    (y₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading y₀)
    (y₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hy₂ : y₂ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading y₁)
    (z : GQ4 K Γ a b c d) :
    y₂ • z = y • z := by
  have hcol : y₂ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) := by
    rw [hy₂, hy₁, hy₀]; rfl
  rw [hcol]
  exact GQ4.bEmbed_smul K Γ a b c d _ y rfl _ rfl _ rfl z

private theorem cEmbed_bundled
    (w₀ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (w' : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading w')
    (w₁ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading w₀)
    (z : GQ4 K Γ a b c d) :
    w₁ • z = w' • z := by
  have hcol : w₁ = GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w') := by
    rw [hw₁, hw₀]; rfl
  rw [hcol]
  exact GQ4.cEmbed_smul K Γ a b c d _ w' rfl _ rfl z

private theorem dEmbed_bundled
    (t₀ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (t : (Γ.D d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading t)
    (z : GQ4 K Γ a b c d) :
    t₀ • z = t • z := by
  have hcol : t₀ = GradedTensorProduct.includeRight
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading t := by
    rw [ht₀]; rfl
  rw [hcol]
  exact GQ4.dEmbed_smul K Γ a b c d _ t rfl z

end GQ4

/-! ### The `⊆` direction: `gQuadInterSpace`'s conditions imply
`gQuadEnv`-super-equivariance -/

/-- The `(A,B) → ((A,B),C)` envelope-source embed, as a single `AlgHom`. -/
private noncomputable def ιAB :
    ((Γ.D a).grading ᵍ⊗[K] (Γ.D b).grading) →ₐ[K]
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
  (GradedTensorProduct.includeLeft
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading).comp
    (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading)

/-- The `(AB,C) → ((AB,C),D)` envelope-source embed. -/
private noncomputable def ιABC :
    (((Γ.D a).gtensor (Γ.D b)).grading ᵍ⊗[K] (Γ.D c).grading) →ₐ[K]
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
  GradedTensorProduct.includeLeft (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
    (Γ.D d).grading

/-- The identity, re-typed from the RAW `ABC.grading ᵍ⊗ D.grading` to the
envelope's own SOURCE carrier — `rfl`-equal but not `instances`
-transparently equal, so `AlgHom.id` itself does not typecheck against the
mismatched instance packaging (mirrors `Bimod.QuadInterface2`'s `ιABCD`). -/
private noncomputable def ιABCD :
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading ᵍ⊗[K] (Γ.D d).grading) →ₐ[K]
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {K} {Γ} {a b c d}

/-- **The `⊆` direction, envelope-source-level equivariance**: the four
slot super-equivariances assemble, via `superEquivariantAt_of_includeLeft_includeRight`
applied at the envelope source's own three internal levels (`(A,B)`,
`(AB,C)`, `(ABC,D)`, all landing at `T :=` the envelope source's own
carrier), chained through `GQ1.aEmbed`–`GQ1.dEmbed`/`GQ4_aEmbed_bundled`–
`_dEmbed_bundled`, into super-equivariance for the envelope source's OWN
action on `GQ1`/`GQ4`, at EVERY homogeneous element (not merely
generators). -/
theorem gQuadSource_equivariant_of_slots {e : ZMod 2} {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d}
    (ha : f ∈ superEquivariant (Γ.D a).grading e)
    (hb : f ∈ superEquivariant (Γ.D b).grading e)
    (hc : f ∈ superEquivariant (Γ.D c).grading e)
    (hd : f ∈ superEquivariant (Γ.D d).grading e) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier⦄,
      w ∈ ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading i →
      ∀ m : GQ1 K Γ a b c d, f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_superEquivariant] at ha hb hc hd
  have hAB := superEquivariantAt_of_includeLeft_includeRight
      (Γ.D a).grading (Γ.D b).grading (ιAB K Γ a b c d)
      (f := f) (e := e)
      (fun j x hx m => by
        have hcol : ιAB K Γ a b c d
            (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
          = GradedTensorProduct.includeLeft
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading
              (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
                  (Γ.D c).grading
                (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)) := rfl
        rw [hcol, GQ1.aEmbed K Γ a b c d _ x rfl _ rfl _ rfl,
          GQ4.aEmbed_bundled K Γ a b c d _ x rfl _ rfl _ rfl]
        exact ha hx m)
      (fun k y hy m => by
        have hcol : ιAB K Γ a b c d
            (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
          = GradedTensorProduct.includeLeft
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading
              (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
                  (Γ.D c).grading
                (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)) := rfl
        rw [hcol, GQ1.bEmbed K Γ a b c d _ y rfl _ rfl _ rfl,
          GQ4.bEmbed_bundled K Γ a b c d _ y rfl _ rfl _ rfl]
        exact hb hy m)
  have hABC := superEquivariantAt_of_includeLeft_includeRight
      ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading (ιABC K Γ a b c d)
      (f := f) (e := e)
      (fun j w hw m => by
        have hcol : ιABC K Γ a b c d
            (GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
              (Γ.D c).grading w)
          = ιAB K Γ a b c d w := rfl
        rw [hcol]
        exact hAB hw m)
      (fun k w' hw' m => by
        have hcol : ιABC K Γ a b c d
            (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
              (Γ.D c).grading w')
          = GradedTensorProduct.includeLeft
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading
              (GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
                (Γ.D c).grading w') := rfl
        rw [hcol, GQ1.cEmbed K Γ a b c d _ w' rfl _ rfl,
          GQ4.cEmbed_bundled K Γ a b c d _ w' rfl _ rfl]
        exact hc hw' m)
  have hABCD := superEquivariantAt_of_includeLeft_includeRight
      (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading (ιABCD K Γ a b c d)
      (f := f) (e := e)
      (fun j w hw m => by
        have hcol : (ιABCD K Γ a b c d)
            (GradedTensorProduct.includeLeft
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading w)
          = ιABC K Γ a b c d w := rfl
        rw [hcol]
        exact hABC hw m)
      (fun k t ht m => by
        have hcol : (ιABCD K Γ a b c d)
            (GradedTensorProduct.includeRight
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading t)
          = GradedTensorProduct.includeRight
              (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading t := rfl
        rw [hcol, GQ1.dEmbed K Γ a b c d _ t rfl, GQ4.dEmbed_bundled K Γ a b c d _ t rfl]
        exact hd ht m)
  intro i w hw m
  exact hABCD hw m

variable (K) (Γ) (a b c d)

/-- The associativity recast of the total coefficient algebra between
`GQ1`'s outer right-coefficient tower `D_{((a+b)+c)+d}` and `GQ4`'s
`D_{a+(b+c+d)}` — reproved locally since `PentagonMembership.lean`'s
`quadRightCast_eq` is `private` (any two proofs of the same equality are
interchangeable, by proof irrelevance). -/
private theorem quadRightCast_eq2 : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- **The `⊇` direction, sixth condition**: a `gQuadEnv`-super-equivariant
`f` of degree `e` satisfies `gQuadInterSpace`'s `rightSemilinear` condition
— the sop-generator instance of `hequiv`, converted via the general
right-sign reconciliation (`rightActionHom_equivariant_iff_rightSemilinear`)
at each homogeneous `τ`, then extended to an arbitrary `t` by
`DirectSum.Decomposition.inductionOn` (linearity in `t`). -/
theorem rightSemilinear_of_gQuadEnv {e : ZMod 2} {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d}
    (hgrad : f ∈ homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) e)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    f ∈ rightSemilinear
        ((Γ.gaugeCast (quadRightCast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom) := by
  have hsop : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c + d)).carrier⦄,
      τ ∈ (Γ.D (a + b + c + d)).grading j → ∀ m : GQ1 K Γ a b c d,
        f (rightActionHom (Γ.D (a + b + c + d)).grading (GQ1.grading K Γ a b c d)
            (SuperOp.op _ τ) m)
          = ((sgn (e * j) : ℤˣ) : ℤ) •
              rightActionHom (Γ.D (a + b + c + d)).grading (GQ4.grading K Γ a b c d)
                (SuperOp.op _ τ) (f m) := by
    intro j τ hτ m
    have hmem := Superfusion.includeRight_mem_tensorGrading
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading) hτ
    have key := hequiv hmem m
    rwa [GQ1_gQuadEnv_smul_def, actionHom_includeRight_apply, GQ4_gQuadEnv_smul_def,
      actionHom_includeRight_apply] at key
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c + d)).carrier⦄,
      τ ∈ (Γ.D (a + b + c + d)).grading j → ∀ m : GQ1 K Γ a b c d,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    exact (rightActionHom_equivariant_iff_rightSemilinear (Γ.D (a + b + c + d)).grading
      (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) hgrad hτ).mp (hsop hτ) m
  rw [mem_rightSemilinear]
  intro t m
  show f (MulOpposite.op t • m)
    = MulOpposite.op ((Γ.gaugeCast (quadRightCast_eq2 a b c d)).toAlgEquiv t) • f m
  induction t using DirectSum.Decomposition.inductionOn (Γ.D (a + b + c + d)).grading with
  | zero => simp [map_zero, MulOpposite.op_zero, zero_smul]
  | homogeneous t' => exact hunsigned t'.2 m
  | add t1 t2 h1 h2 => simp only [MulOpposite.op_add, add_smul, map_add]; rw [h1, h2]

/-- **The `⊇` direction, assembled**: a `f ∈ gradedHomF` (i.e.
`gQuadEnv`-homogeneous and `gQuadEnv`-super-equivariant of degree `e`)
satisfies all six of `gQuadInterSpace`'s conditions. -/
theorem gQuadInterSpace_of_mem_gradedHomF {e : ZMod 2}
    {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d}
    (hf : f ∈ gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
      (GQ4.grading K Γ a b c d) e) :
    f ∈ gQuadInterSpace K Γ a b c d e := by
  obtain ⟨hgrad, ha, hb, hc, hd⟩ := gQuadInterSpace_five_conditions_of_mem_gradedHomF hf
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨_, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  rw [mem_gQuadInterSpace_iff]
  exact ⟨hgrad, ha, hb, hc, hd, rightSemilinear_of_gQuadEnv K Γ a b c d hgrad hequiv⟩

set_option maxHeartbeats 1000000 in
/-- **The `⊆` direction, assembled**: all six `gQuadInterSpace` conditions
(`homGrading`, the four slot super-equivariances, and `rightSemilinear`)
assemble into full `gQuadEnv`-super-equivariance — the source-level
equivariance of `gQuadSource_equivariant_of_slots` supplies `hL` (via
`GQ1_gQuadEnv_smul_def`/`GQ4_gQuadEnv_smul_def` + `actionHom_includeLeft_apply`,
since `gQuadEnv`, unlike the envelope source, is a plain `abbrev` for the
RAW graded tensor product, so `AlgHom.id` typechecks against it directly
with no instance mismatch); `hR` is the sop-generator condition of the
general right-sign reconciliation, reconciled with `rightSemilinear` via
`GQ4.rightRecast_op_smul_def` (`QuadEnvModule2.lean`). -/
theorem gQuadEnv_equivariant_of_gQuadInterSpace
    {e : ZMod 2} {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d}
    (hgrad : f ∈ homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) e)
    (ha : f ∈ superEquivariant (Γ.D a).grading e)
    (hb : f ∈ superEquivariant (Γ.D b).grading e)
    (hc : f ∈ superEquivariant (Γ.D c).grading e)
    (hd : f ∈ superEquivariant (Γ.D d).grading e)
    (hR : f ∈ rightSemilinear
        ((Γ.gaugeCast (quadRightCast_eq2 a b c d)).toAlgEquiv.toAlgHom.toRingHom)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m) := by
  rw [mem_rightSemilinear] at hR
  have hslots := gQuadSource_equivariant_of_slots ha hb hc hd
  have hunsigned : ∀ ⦃j : ZMod 2⦄ ⦃τ : (Γ.D (a + b + c + d)).carrier⦄,
      τ ∈ (Γ.D (a + b + c + d)).grading j → ∀ m : GQ1 K Γ a b c d,
        f (MulOpposite.op τ • m) = MulOpposite.op τ • f m := by
    intro j τ hτ m
    rw [GQ4.rightRecast_op_smul_def]
    exact hR τ m
  exact superEquivariantAt_of_includeLeft_includeRight
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (SuperOp.grading (Γ.D (a + b + c + d)).grading)
    (AlgHom.id K (gQuadEnv K Γ a b c d)) (f := f) (e := e)
    (fun j x hx m => by
      have hcol : (AlgHom.id K (gQuadEnv K Γ a b c d))
          (GradedTensorProduct.includeLeft
            ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
            (SuperOp.grading (Γ.D (a + b + c + d)).grading) x)
        = GradedTensorProduct.includeLeft
            ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
            (SuperOp.grading (Γ.D (a + b + c + d)).grading) x := rfl
      rw [hcol, GQ1_gQuadEnv_smul_def, actionHom_includeLeft_apply,
        GQ4_gQuadEnv_smul_def, actionHom_includeLeft_apply]
      exact hslots hx m)
    (fun k τ hτ m => by
      have hcol : (AlgHom.id K (gQuadEnv K Γ a b c d))
          (GradedTensorProduct.includeRight
            ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
            (SuperOp.grading (Γ.D (a + b + c + d)).grading) τ)
        = GradedTensorProduct.includeRight
            ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
            (SuperOp.grading (Γ.D (a + b + c + d)).grading) τ := rfl
      rw [hcol, GQ1_gQuadEnv_smul_def, actionHom_includeRight_apply,
        GQ4_gQuadEnv_smul_def, actionHom_includeRight_apply]
      set τ' := SuperOp.unop (Γ.D (a + b + c + d)).grading τ with hτ'def
      have hτ'mem : τ' ∈ (Γ.D (a + b + c + d)).grading k := hτ
      rw [show τ = SuperOp.op (Γ.D (a + b + c + d)).grading τ'
          from (SuperOp.op_unop (Γ.D (a + b + c + d)).grading τ).symm]
      exact (rightActionHom_equivariant_iff_rightSemilinear (Γ.D (a + b + c + d)).grading
        (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) hgrad hτ'mem).mpr
        (hunsigned hτ'mem) m)

/-! ### The interface, assembled -/

/-- **`mem_gQuadInterSpace_iff_gradedHomF`**: `gQuadInterSpace`'s six
conditions (`homGrading`, the four slot super-equivariances,
`rightSemilinear`) are EXACTLY `gradedHomF`'s two (`homGrading` and
`gQuadEnv`-super-equivariance) — the interface completing this milestone.
`⊇` is `gQuadInterSpace_of_mem_gradedHomF`; `⊆` assembles
`gQuadEnv_equivariant_of_gQuadInterSpace` (the four slots plus
`rightSemilinear` give full `gQuadEnv`-equivariance) with the verbatim
`homGrading` match. -/
theorem mem_gQuadInterSpace_iff_gradedHomF {e : ZMod 2}
    {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d} :
    f ∈ gQuadInterSpace K Γ a b c d e ↔
      f ∈ gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
        (GQ4.grading K Γ a b c d) e := by
  constructor
  · intro hf
    rw [mem_gQuadInterSpace_iff] at hf
    obtain ⟨hgrad, ha, hb, hc, hd, hR⟩ := hf
    rw [mem_gradedHomF_iff, mem_superEquivariant]
    exact ⟨hgrad, gQuadEnv_equivariant_of_gQuadInterSpace K Γ a b c d hgrad ha hb hc hd hR⟩
  · exact gQuadInterSpace_of_mem_gradedHomF K Γ a b c d

end GaugeChi

end Superfusion
