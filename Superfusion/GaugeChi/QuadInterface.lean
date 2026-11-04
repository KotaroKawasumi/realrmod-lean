/-
Superfusion / GaugeChi / QuadInterface

Milestone M12-7 of the abstract `(p, χ)` arc: **the quadruple interface,
stage one** — `GQ1`'s four slot-embedding bridges `aEmbed`–`dEmbed` (the
Γ-mirror of `Superfusion.Bimod.QuadInterface`'s `Q1` section, one gtensor
level up from `GaugeChi.GaugeParity`'s `GBL` section), together with the
envelope-gradedness / `SMulCommClass`/`IsScalarTower` scaffolding both
`GQ1` and `GQ4` need against `gQuadEnv`, and the `⊇`-direction four-slot
assembly `gQuadInterSpace_five_conditions_of_mem_gradedHomF` — everything
short of `rightSemilinear` and the `⊆` direction, which need `GQ4`'s
BUNDLED embed bridges and land in `QuadInterface2.lean`.

`GQ1`'s combined `gQuadEnv`-action already has the envelope's own bracket
`((D_a ᵍ⊗ D_b) ᵍ⊗ D_c) ᵍ⊗ D_d` (`QuadEnvModule.lean`'s STRUCTURAL route), so
a single further collapse of `gtensorLeftActionHom` — chained through
`GBL`'s own `aEmbed`/`bEmbed`/`cEmbed` (`GaugeChi.GaugeParity`) for the
inner three slots, and directly via `gtensorLeftActionHom_includeRight` for
the outer `d`-slot (`GQ1`'s own direct middle slot,
`GaugeChi.PentagonActions`) — produces `aEmbed`–`dEmbed`, mirroring
`Bimod.QuadInterface`'s `Q1` section verbatim, one gtensor level up from
`GBL`'s own three-slot precedent.  `GQ4`'s matching bridges (`aEmbed_smul`–
`dEmbed_smul`, the DIRECT-LIFT route) were added to `QuadEnvModule2.lean`
this round (mirroring `Bimod.QuadEnvModule2`'s `Q4.aEmbed_smul`–
`_dEmbed_smul`), so the `⊇`-direction four-slot assembly below uses them
directly — no bundling needed there (bundling is only required for the `⊆`
direction's `AlgHom`-mediated route, `QuadInterface2.lean`).
-/
import Superfusion.GaugeChi.QuadEnvModule2
import Superfusion.GaugeChi.PentagonMembership

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c d : G)

/-! ### The tensor grading of `gQuadEnv`'s own envelope tensor -/

/-- The tensor grading of `gQuadEnv`'s own envelope tensor
(`Superfusion.tensorGrading`, M7f-1a's grading making `𝒜 ᵍ⊗ ℬ` a graded
algebra) — the grading `superEquivariant`/`gradedHomF` quantify over when
`𝒯 := gQuadEnv K Γ a b c d`. -/
noncomputable abbrev gQuadEnvGrading : ZMod 2 → Submodule K (gQuadEnv K Γ a b c d) :=
  Superfusion.tensorGrading
    ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
    (SuperOp.grading (Γ.D (a + b + c + d)).grading)

namespace GQ1

/-- **`GQ1`'s `gQuadEnv`-action is graded**: `actionHom_mem_tensorGrading`
instantiated at `GQ1`'s own `gQuadEnv`-module structure
(`instModuleGQuadEnv`, `QuadEnvModule.lean`). -/
instance : SetLike.GradedSMul (gQuadEnvGrading K Γ a b c d) (grading K Γ a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end GQ1

namespace GQ4

/-- **`GQ4`'s `gQuadEnv`-action is graded**. -/
instance : SetLike.GradedSMul (gQuadEnvGrading K Γ a b c d) (grading K Γ a b c d) where
  smul_mem {i j} w z hw hz := by
    rw [vadd_eq_add]
    exact actionHom_mem_tensorGrading _ _ _ hw hz

end GQ4

theorem GQ1_gQuadEnv_smul_def (w : gQuadEnv K Γ a b c d) (m : GQ1 K Γ a b c d) :
    w • m = actionHom ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (Γ.D (a + b + c + d)).grading (GQ1.grading K Γ a b c d) w m := rfl

theorem GQ4_gQuadEnv_smul_def (w : gQuadEnv K Γ a b c d) (m : GQ4 K Γ a b c d) :
    w • m = actionHom ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (Γ.D (a + b + c + d)).grading (GQ4.grading K Γ a b c d) w m := rfl

/-- `SMulCommClass K (gQuadEnv K Γ a b c d) (GQ1 K Γ a b c d)`: `actionHom
w` is already `K`-linear for every fixed `w`, since it is a bundled
`M →ₗ[K] M` map by construction. Needed for `gradedHomF`'s own
`[SMulCommClass K T N]` hypothesis. -/
instance : SMulCommClass K (gQuadEnv K Γ a b c d) (GQ1 K Γ a b c d) :=
  ⟨fun k w m => (map_smul (actionHom
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (Γ.D (a + b + c + d)).grading (GQ1.grading K Γ a b c d) w) k m).symm⟩

instance : SMulCommClass K (gQuadEnv K Γ a b c d) (GQ4 K Γ a b c d) :=
  ⟨fun k w m => (map_smul (actionHom
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (Γ.D (a + b + c + d)).grading (GQ4.grading K Γ a b c d) w) k m).symm⟩

/-- `K` is a scalar tower for `gQuadEnv K Γ a b c d` on `GQ1`/`GQ4` —
needed as the `[IsScalarTower K T M] [IsScalarTower K T N]` hypothesis of
`superEquivariantAt_of_includeLeft_includeRight` at the OUTER (sop-tensor)
level. -/
instance : IsScalarTower K (gQuadEnv K Γ a b c d) (GQ1 K Γ a b c d) :=
  ⟨fun k w m => by simp only [GQ1_gQuadEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

instance : IsScalarTower K (gQuadEnv K Γ a b c d) (GQ4 K Γ a b c d) :=
  ⟨fun k w m => by simp only [GQ4_gQuadEnv_smul_def, map_smul, LinearMap.smul_apply]⟩

/-! ### `GQ1`'s four slot-embedding bridges -/

namespace GQ1

theorem aslot_apply (x : (Γ.D a).carrier) (z : GQ1 K Γ a b c d) :
    x • z = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) x z := rfl

theorem bslot_apply (y : (Γ.D b).carrier) (z : GQ1 K Γ a b c d) :
    y • z = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) y z := rfl

theorem cslot_apply (w : (Γ.D c).carrier) (z : GQ1 K Γ a b c d) :
    w • z = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
      (FusionColumn (Γ.fuse (a + b + c) d)) w z := rfl

theorem dslot_apply (t : (Γ.D d).carrier) (z : GQ1 K Γ a b c d) :
    t • z = midAlgHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) t z := rfl

/-- `GQ1`'s combined action at the bridged `.gtensor.carrier` spelling,
elementwise (`rfl`, matching the spelling the embedding lemmas below
need). -/
theorem gtensorABCD_smul_def
    (w : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (m : GQ1 K Γ a b c d) :
    w • m = gtensorLeftActionHom (Γ.D (a + b + c)).grading (GBL.grading Γ a b c)
      (Γ.D d).grading (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) w m := rfl

/-- **The `a`-slot-embedding bridge**: the envelope-source element
obtained by embedding `x : D_a` via the three-fold `includeLeft` chain
matching the envelope's own bracket order acts on `GQ1`, on *every*
element, exactly as `GQ1`'s own registered `a`-slot action of `x`. -/
theorem aEmbed
    (x₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (x : (Γ.D a).carrier)
    (hx₀ : x₀ = GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x)
    (x₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hx₁ : x₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading x₀)
    (x₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hx₂ : x₂ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading x₁)
    (z : GQ1 K Γ a b c d) :
    x₂ • z = x • z := by
  have key : (leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) x₁ : Module.End K (GQ1 K Γ a b c d))
      = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D a).carrier) x := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, GBL.aEmbed K Γ a b c x₀ x hx₀ x₁ hx₁]
  rw [gtensorABCD_smul_def, hx₂, gtensorLeftActionHom_includeLeft, key, ← aslot_apply]

/-- **The `b`-slot-embedding bridge**. -/
theorem bEmbed
    (y₀ : ((Γ.D a).gtensor (Γ.D b)).carrier) (y : (Γ.D b).carrier)
    (hy₀ : y₀ = GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y)
    (y₁ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (hy₁ : y₁ = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading y₀)
    (y₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hy₂ : y₂ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading y₁)
    (z : GQ1 K Γ a b c d) :
    y₂ • z = y • z := by
  have key : (leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) y₁ : Module.End K (GQ1 K Γ a b c d))
      = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D b).carrier) y := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, GBL.bEmbed K Γ a b c y₀ y hy₀ y₁ hy₁]
  rw [gtensorABCD_smul_def, hy₂, gtensorLeftActionHom_includeLeft, key, ← bslot_apply]

/-- **The `c`-slot-embedding bridge**. -/
theorem cEmbed
    (w₀ : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) (w' : (Γ.D c).carrier)
    (hw₀ : w₀ = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading w')
    (w₁ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (hw₁ : w₁ = GradedTensorProduct.includeLeft
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading w₀)
    (z : GQ1 K Γ a b c d) :
    w₁ • z = w' • z := by
  have key : (leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) w₀ : Module.End K (GQ1 K Γ a b c d))
      = leftActionEnd K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) (B := (Γ.D c).carrier) w' := by
    refine RelTensor.hom_ext fun u v => ?_
    rw [leftActionEnd_mk, leftActionEnd_mk, GBL.cEmbed K Γ a b c w₀ w' hw₀]
  rw [gtensorABCD_smul_def, hw₁, gtensorLeftActionHom_includeLeft, key, ← cslot_apply]

/-- **The `d`-slot-embedding bridge** — a single (`GQ1`-level) collapse,
since `D_d` is `GQ1`'s own direct middle slot, no `GBL` level involved. -/
theorem dEmbed
    (t₀ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier)
    (t : (Γ.D d).carrier)
    (ht₀ : t₀ = GradedTensorProduct.includeRight
        (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading (Γ.D d).grading t)
    (z : GQ1 K Γ a b c d) :
    t₀ • z = t • z := by
  rw [gtensorABCD_smul_def, ht₀, gtensorLeftActionHom_includeRight, ← dslot_apply]

end GQ1

/-! ### The interface, `⊇` direction: the four slot conditions -/

variable {K} {Γ} {a b c d}

/-- **The `⊇` direction, `a`-slot**: a `gQuadEnv`-super-equivariant `f`
of degree `e` is super-equivariant for the `D_a`-slot action, of the same
degree. -/
theorem superEquivariant_a_of_gQuadEnv {e : ZMod 2} (f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D a).carrier⦄, x ∈ (Γ.D a).grading i →
      ∀ m : GQ1 K Γ a b c d, f (x • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • f m) := by
  intro i x hx m
  have hx0mem := Superfusion.includeLeft_mem_tensorGrading (Γ.D a).grading (Γ.D b).grading hx
  have hx1mem := Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading hx0mem
  set x₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x))
    with hx2def
  have hx2mem : x₂ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading i := by
    rw [hx2def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading hx1mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading) hx2mem
  have key := hequiv hwmem m
  rw [GQ1_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ1.aEmbed K Γ a b c d
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) x rfl
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x))
      rfl x₂ hx2def] at key
  rw [key, GQ4_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ4.aEmbed_smul K Γ a b c d
      (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) x rfl
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x))
      rfl x₂ hx2def]

/-- **The `⊇` direction, `b`-slot**. -/
theorem superEquivariant_b_of_gQuadEnv {e : ZMod 2} (f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D b).carrier⦄, y ∈ (Γ.D b).grading i →
      ∀ m : GQ1 K Γ a b c d, f (y • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • f m) := by
  intro i y hy m
  have hy0mem := Superfusion.includeRight_mem_tensorGrading (Γ.D a).grading (Γ.D b).grading hy
  have hy1mem := Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading hy0mem
  set y₂ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y))
    with hy2def
  have hy2mem : y₂ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading i := by
    rw [hy2def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading hy1mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading) hy2mem
  have key := hequiv hwmem m
  rw [GQ1_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ1.bEmbed K Γ a b c d
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) y rfl
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y))
      rfl y₂ hy2def] at key
  rw [key, GQ4_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ4.bEmbed_smul K Γ a b c d
      (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) y rfl
      (GradedTensorProduct.includeLeft
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y))
      rfl y₂ hy2def]

/-- **The `⊇` direction, `c`-slot**. -/
theorem superEquivariant_c_of_gQuadEnv {e : ZMod 2} (f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃w' : (Γ.D c).carrier⦄, w' ∈ (Γ.D c).grading i →
      ∀ m : GQ1 K Γ a b c d, f (w' • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w' • f m) := by
  intro i w' hw' m
  have hw0mem := Superfusion.includeRight_mem_tensorGrading
      (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading hw'
  set w₁ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
    GradedTensorProduct.includeLeft
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading
      (GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w')
    with hw1def
  have hw1mem : w₁ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading i := by
    rw [hw1def]
    exact Superfusion.includeLeft_mem_tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading hw0mem
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading) hw1mem
  have key := hequiv hwmem m
  rw [GQ1_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ1.cEmbed K Γ a b c d
      (GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w')
      w' rfl w₁ hw1def] at key
  rw [key, GQ4_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ4.cEmbed_smul K Γ a b c d
      (GradedTensorProduct.includeRight
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading w')
      w' rfl w₁ hw1def]

/-- **The `⊇` direction, `d`-slot** — a single (`GQ1`/`GQ4`-level)
collapse, since `D_d` is the envelope source's own outermost right
factor. -/
theorem superEquivariant_d_of_gQuadEnv {e : ZMod 2} (f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d)
    (hequiv : ∀ ⦃i : ZMod 2⦄ ⦃w : gQuadEnv K Γ a b c d⦄,
      w ∈ gQuadEnvGrading K Γ a b c d i → ∀ m : GQ1 K Γ a b c d,
        f (w • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (w • f m)) :
    ∀ ⦃i : ZMod 2⦄ ⦃t : (Γ.D d).carrier⦄, t ∈ (Γ.D d).grading i →
      ∀ m : GQ1 K Γ a b c d, f (t • m) = ((sgn (e * i) : ℤˣ) : ℤ) • (t • f m) := by
  intro i t ht m
  set t₀ : ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).carrier :=
    GradedTensorProduct.includeRight
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading t
    with ht0def
  have ht0mem : t₀ ∈ Superfusion.tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading i := by
    rw [ht0def]
    exact Superfusion.includeRight_mem_tensorGrading
      (Superfusion.tensorGrading
        (Superfusion.tensorGrading (Γ.D a).grading (Γ.D b).grading) (Γ.D c).grading)
      (Γ.D d).grading ht
  have hwmem := Superfusion.includeLeft_mem_tensorGrading
      ((((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).gtensor (Γ.D d)).grading
      (SuperOp.grading (Γ.D (a + b + c + d)).grading) ht0mem
  have key := hequiv hwmem m
  rw [GQ1_gQuadEnv_smul_def, actionHom_includeLeft_apply, GQ1.dEmbed K Γ a b c d t₀ t ht0def] at key
  rw [key, GQ4_gQuadEnv_smul_def, actionHom_includeLeft_apply,
    GQ4.dEmbed_smul K Γ a b c d t₀ t ht0def]

/-- **The `⊇` direction, assembled**: a `f ∈ gradedHomF` (i.e.
`gQuadEnv`-homogeneous of degree `e` and `gQuadEnv`-super-equivariant of
degree `e`) satisfies `gQuadInterSpace`'s five non-`rightSemilinear`
conditions — `homGrading` (verbatim, same descended gradings) and the four
slot super-equivariances (`superEquivariant_a_of_gQuadEnv`–
`_d_of_gQuadEnv`).  `rightSemilinear` is finished in `QuadInterface2.lean`. -/
theorem gQuadInterSpace_five_conditions_of_mem_gradedHomF {e : ZMod 2}
    {f : GQ1 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d}
    (hf : f ∈ gradedHomF (GQ1.grading K Γ a b c d) (gQuadEnvGrading K Γ a b c d)
      (GQ4.grading K Γ a b c d) e) :
    f ∈ homGrading (GQ1.grading K Γ a b c d) (GQ4.grading K Γ a b c d) e
      ∧ f ∈ superEquivariant (Γ.D a).grading e
      ∧ f ∈ superEquivariant (Γ.D b).grading e
      ∧ f ∈ superEquivariant (Γ.D c).grading e
      ∧ f ∈ superEquivariant (Γ.D d).grading e := by
  rw [mem_gradedHomF_iff] at hf
  obtain ⟨hgrad, hequiv⟩ := hf
  rw [mem_superEquivariant] at hequiv
  exact ⟨hgrad, superEquivariant_a_of_gQuadEnv f hequiv, superEquivariant_b_of_gQuadEnv f hequiv,
    superEquivariant_c_of_gQuadEnv f hequiv, superEquivariant_d_of_gQuadEnv f hequiv⟩

end GaugeChi

end Superfusion
