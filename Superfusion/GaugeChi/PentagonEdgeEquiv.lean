/-
Superfusion / GaugeChi / PentagonEdgeEquiv

Milestone M12-4 of the abstract `(p, χ)` arc (continued): **equivariance of
the pentagon edges** — the Γ-mirror of `Superfusion.Bimod.EdgeEquiv`–
`EdgeEquiv5.lean`/`EdgeEquivClose.lean`, transporting the four slot actions
and the right action of `GaugeChi.PentagonActions` through the five edges
`GE1`–`GE5` and the closing connector `gq4Close`
(`GaugeChi.Pentagon`/`PentagonEdges`).

Every sign law is IDENTICAL to the tower's: the signs come from the general
`smap`/`RelTensor.map` machinery (already Γ-general), not from `ZMod 8`, so
the closed forms below are literal transcriptions of `EdgeEquiv*.lean`'s
generator-level lemmas — `GE1` alone descends cleanly through the general
`End`-composition lemmas (`Bimod.MapEquivariance`); `GE2`–`GE5` and
`gq4Close` each fold their own associator/swap/recast into their generator
formula, so their transport laws are established at the generator level
(a specific internal factor homogeneous — the "generator-∀" style, mirroring
the tower's own scoping note), by unfolding through the slot laws of `GBL`,
`GBR` (`GaugeChi.RouteBimod`) and of the two endpoint vertices
(`GaugeChi.PentagonActions`).
-/
import Superfusion.GaugeChi.PentagonActions
import Superfusion.GaugeChi.PentagonEdges
import Superfusion.Bimod.MapEquivariance

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

/-- `Γ.gaugeCast` preserves grading membership (a direct corollary of
`SuperAlgEquiv.map_grading`). -/
theorem gaugeCast_mem_grading {x y : G} (h : x = y) {i : ZMod 2} {v : (Γ.D x).carrier}
    (hv : v ∈ (Γ.D x).grading i) :
    (Γ.gaugeCast h).toAlgEquiv v ∈ (Γ.D y).grading i :=
  Γ.gaugeCast_mem_grading h hv

/-! ### The first pentagon edge -/

namespace GE1

variable (t : GBL Γ a b c →ₗ[K] GBR Γ a b c)
variable (ht : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
  t (MulOpposite.op τ • m) = MulOpposite.op τ • t m)

/-- `GE1` transports a slot action through the route factor, with `t`'s own
equivariance scalar (`a`, `b`, `c`-slots alike). -/
theorem comp_aslot {s : ℤ} {x : (Γ.D a).carrier}
    (htA : ∀ m : GBL Γ a b c, t (x • m) = s • (x • t m))
    (z : GQ1 K Γ a b c d) :
    GE1 K Γ a b c d t ht (x • z) = s • (x • GE1 K Γ a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (Γ.D a).carrier) htA)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

theorem comp_bslot {s : ℤ} {y : (Γ.D b).carrier}
    (htB : ∀ m : GBL Γ a b c, t (y • m) = s • (y • t m))
    (z : GQ1 K Γ a b c d) :
    GE1 K Γ a b c d t ht (y • z) = s • (y • GE1 K Γ a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (Γ.D b).carrier) htB)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

theorem comp_cslot {s : ℤ} {z₀ : (Γ.D c).carrier}
    (htC : ∀ m : GBL Γ a b c, t (z₀ • m) = s • (z₀ • t m))
    (z : GQ1 K Γ a b c d) :
    GE1 K Γ a b c d t ht (z₀ • z) = s • (z₀ • GE1 K Γ a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (Γ.D c).carrier) htC)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

/-- `GE1` transports the `d`-slot middle action up to the sign `(-1)^{e|τ|}`
of `t`'s degree shift. -/
theorem comp_dslot {e : ZMod 2}
    (hte : ∀ j : ZMod 2, ∀ m ∈ GBL.grading Γ a b c j, t m ∈ GBR.grading Γ a b c (j + e))
    {k : ZMod 2} {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading k) (z : GQ1 K Γ a b c d) :
    GE1 K Γ a b c d t ht (τ • z)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (τ • GE1 K Γ a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_midEnd t LinearMap.id
      (Γ.D (a + b + c)).grading (GBL.grading Γ a b c) (GBR.grading Γ a b c)
      (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))
      ht (fun _ _ => rfl) hte hτ (fun _ => rfl))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

/-- `GE1` transports the right action plainly. -/
theorem comp_right (τ : ((Γ.D (a + b + c + d)).carrier)ᵐᵒᵖ) (z : GQ1 K Γ a b c d) :
    GE1 K Γ a b c d t ht (τ • z) = τ • GE1 K Γ a b c d t ht z := by
  have h' := congrArg (fun F => F z)
    (map_comp_rightActionEnd t LinearMap.id ht (fun _ _ => rfl) (e := τ) (fun _ => rfl))
  simp only [LinearMap.comp_apply] at h'
  exact h'

/-- `GE1` is homogeneous of `t`'s degree. -/
theorem mem_grading {e : ZMod 2}
    (hte : ∀ j : ZMod 2, ∀ m ∈ GBL.grading Γ a b c j, t m ∈ GBR.grading Γ a b c (j + e))
    {i : ZMod 2} {z : GQ1 K Γ a b c d} (hz : z ∈ GQ1.grading K Γ a b c d i) :
    GE1 K Γ a b c d t ht z ∈ GQ2.grading K Γ a b c d (i + e) := by
  have h := map_mem_relGrading_of_degree t LinearMap.id
    (GBL.grading Γ a b c) (FusionColumn.grading (Γ.fuse (a + b + c) d))
    (GBR.grading Γ a b c) (FusionColumn.grading (Γ.fuse (a + b + c) d))
    ht (fun _ _ => rfl) hte
    (fun j v hv => by rwa [add_zero] : ∀ j : ZMod 2,
      ∀ v ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) j,
        LinearMap.id v ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) (j + 0))
    hz
  rwa [show e + (0 : ZMod 2) = 0 + e from by rw [add_zero, zero_add],
    ← add_assoc, add_zero] at h

end GE1

/-! ### The second pentagon edge -/

namespace GE2

variable (e : ZMod 2) (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
variable (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
  y ∈ (Γ.D (b + c)).grading i →
  ∀ n : GQ2rInner K Γ a b c d,
    t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))

/-- `GE2_mk_of_mem`, restated through the synonym-valued `mk`s of `GQ2`,
`GBR` and `GQ3` (the track's discipline) — bridges the raw `RelTensor.mk`
spelling of `GE2_mk_of_mem` to the generator lemmas of `GQ2` and `GQ3`, by
`rfl` (`GQ2.mk`, `GQ3.mk` unfold to `RelTensor.mk`). -/
private theorem GE2_mk_of_mem' {j : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d u
            (t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) :=
  GE2_mk_of_mem K Γ a b c d e t₂ ht₂ hu v w

/-- `GE2` transports the `b`-slot through the exposed column factor, with the
amplification's own sign — no extra hypothesis on `t₂` is needed, since the
`b`-slot never touches `t₂`'s domain. -/
theorem comp_bslot {i j : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading i)
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (y • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (y • GE2 K Γ a b c d e t₂ ht₂
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)) := by
  have hL : GE2 K Γ a b c d e t₂ ht₂ (y • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * (i + j)) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d (y • u)
            (t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
    rw [GQ2.bslot_smul_mk, GBR.bslot_smul_mk]
    exact GE2_mk_of_mem' K Γ a b c d e t₂ ht₂
      ((vadd_eq_add i j) ▸ SetLike.GradedSMul.smul_mem hy hu) v w
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm y,
    GQ3.bslot_smul_mk, smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `GE2` transports the `c`-slot through the exposed column factor, with the
amplification's own sign. -/
theorem comp_cslot {i j : ZMod 2} {z0 : (Γ.D c).carrier}
    (hz0 : z0 ∈ (Γ.D c).grading i)
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (z0 • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * i) : ℤˣ) : ℤ) •
          (z0 • GE2 K Γ a b c d e t₂ ht₂
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)) := by
  have hL : GE2 K Γ a b c d e t₂ ht₂ (z0 • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * (i + j)) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d (z0 • u)
            (t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
    rw [GQ2.cslot_smul_mk, GBR.cslot_smul_mk]
    exact GE2_mk_of_mem' K Γ a b c d e t₂ ht₂
      ((vadd_eq_add i j) ▸ SetLike.GradedSMul.smul_mem hz0 hu) v w
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm z0,
    GQ3.cslot_smul_mk, smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `GE2` transports the `a`-slot up to `t₂`'s own equivariance scalar `s`
for it — the mid-of-mid Koszul signs of `GQ2` and `GQ3` (both keyed to `u`'s
degree `j`) cancel exactly. -/
theorem comp_aslot {s : ℤ} {k j : ZMod 2}
    {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht₂A : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) (x • v) w)
        = s • (x • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (x • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = s • (x • GE2 K Γ a b c d e t₂ ht₂
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)) := by
  have hL : GE2 K Γ a b c d e t₂ ht₂ (x • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (k * j) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (s • GQ3.mk K Γ a b c d u
            (x • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))) := by
    rw [GQ2.aslot_smul_mk, GBR.aslot_smul_mk_of_mem Γ a b c hx hu, map_zsmul,
      LinearMap.smul_apply, map_zsmul,
      GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu (x • v) w, ht₂A, map_zsmul]
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm x,
    GQ3.aslot_smul_mk_of_mem K Γ a b c d hx hu]
  simp only [smul_smul]
  congr 1
  ring

/-- `GE2` transports the `d`-slot up to `t₂`'s own equivariance scalar `s'`
for it and a residual sign `(-1)^{m|v|}` — `GQ2`'s middle-slot sign is keyed
to the *combined* `GBR`-degree `|u|+|v|` (not `|u|` alone), while `GQ3`'s is
keyed to `|u|` alone, so one factor `(-1)^{m|v|}` survives. -/
theorem comp_dslot {s' : ℤ} {m j jv : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₂D : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v (τ • w))
        = s' • (τ • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    {v : FusionColumn (Γ.fuse a (b + c))} (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (m * jv) : ℤˣ) : ℤ) • s' •
          (τ • GE2 K Γ a b c d e t₂ ht₂
            (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)) := by
  have hL : GE2 K Γ a b c d e t₂ ht₂ (τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (s' • GQ3.mk K Γ a b c d u
            (τ • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
              (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)))) := by
    rw [GQ2.dslot_smul_mk_of_mem K Γ a b c d hτ (GBR.mk_mem_grading Γ a b c hu hv),
      map_zsmul, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v (τ • w), ht₂D, map_zsmul]
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm τ,
    GQ3.dslot_smul_mk_of_mem K Γ a b c d hτ hu, mul_add m j jv, sgn_add,
    Units.val_mul]
  simp only [smul_smul]
  congr 1
  ring

/-! #### The clean-form `d`-slot transport

Rephrasing `GE2`'s `d`-slot transport against `GQ2rInner`'s own **signed**
`d`-slot action (mirroring `GQ1`'s `d`-slot construction, at `GQ2rInner`'s
own spelling of the tower index `D_{(a+b)+c}` rather than `GBR`'s literal
`D_{a+(b+c)}`, since the two are only *propositionally* equal) makes the
residual dissolve exactly. -/

/-- The right coefficient action of `FusionColumn (Γ.fuse a (b+c))`, recast
to `D_{(a+b)+c}`, is graded — the missing `GradedRightSMul` instance needed
to run `midAlgHom` at `GQ2rInner`'s own spelling of the tower index. -/
instance GQ2rInner.recast_gradedRightSMul :
    GradedRightSMul (Γ.D (a + b + c)).grading
      (FusionColumn.grading (Γ.fuse a (b + c))) where
  smul_mem _ _ _ _ hτ hw := by
    rw [fusionColumn_recast_op_smul_def]
    exact GradedRightSMul.smul_mem
      (gaugeCast_mem_grading K Γ (add_assoc a b c) hτ) hw

/-- `GQ2rInner`'s own signed `d`-slot action, mirroring `GQ1`'s `d`-slot
construction at `GQ2rInner`'s own spelling of the tower index
`D_{(a+b)+c}`. -/
noncomputable instance GQ2rInner.dslotModule : Module (Γ.D d).carrier
    (GQ2rInner K Γ a b c d) :=
  Module.compHom
    (RelTensor K (Γ.D (a + b + c)).carrier
      (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)))
    ((midAlgHom (Γ.D (a + b + c)).grading
      (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading
      (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d))).toRingHom)

/-- The sign law of `GQ2rInner`'s own `d`-slot action: for homogeneous `τ`,
`v`, `τ • mk v w = (-1)^{|τ||v|} mk v (τ • w)`. -/
theorem GQ2rInner.dslot_smul_of_mem {jv m : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    {v : FusionColumn (Γ.fuse a (b + c))}
    (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    τ • (RelTensor.mk K (Γ.D (a + b + c)).carrier
          (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
        : GQ2rInner K Γ a b c d)
      = ((sgn (m * jv) : ℤˣ) : ℤ) •
          (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v (τ • w)
          : GQ2rInner K Γ a b c d) :=
  midEnd_mk_of_mem (Γ.D (a + b + c)).grading
    (FusionColumn.grading (Γ.fuse a (b + c))) (Γ.D d).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b + c) d)) hv hτ w

private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

private theorem zmod2_dslot2_deg : ∀ m j jv : ZMod 2,
    m * (j + jv) + m * jv = m * j := by decide

/-- **The clean-form `d`-slot transport**: rephrased against `GQ2rInner`'s
own signed `d`-slot action (`ht₂D'`), `GE2`'s `d`-slot transport is
*component-independent* — `t₂`'s own equivariance scalar `s'`, with no
residual sign at all. -/
theorem comp_dslot' {s' : ℤ} {m j jv : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₂D' : ∀ x : GQ2rInner K Γ a b c d,
      t₂ (τ • x) = s' • (τ • t₂ x))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    {v : FusionColumn (Γ.fuse a (b + c))} (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂ (τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = s' • (τ • GE2 K Γ a b c d e t₂ ht₂
          (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)) := by
  have hX : (RelTensor.mk K (Γ.D (a + b + c)).carrier
        (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v (τ • w)
        : GQ2rInner K Γ a b c d)
      = ((sgn (m * jv) : ℤˣ) : ℤ) •
          (τ • (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w
            : GQ2rInner K Γ a b c d)) := by
    rw [GQ2rInner.dslot_smul_of_mem K Γ a b c d hτ hv, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have hL : GE2 K Γ a b c d e t₂ ht₂ (τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) • (((sgn (e * j) : ℤˣ) : ℤ) •
          (((sgn (m * jv) : ℤˣ) : ℤ) •
            (s' • GQ3.mk K Γ a b c d u
              (τ • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))))) := by
    rw [GQ2.dslot_smul_mk_of_mem K Γ a b c d hτ (GBR.mk_mem_grading Γ a b c hu hv),
      map_zsmul, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v (τ • w), hX, map_zsmul,
      ht₂D', map_zsmul, map_zsmul]
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm τ,
    GQ3.dslot_smul_mk_of_mem K Γ a b c d hτ hu]
  simp only [smul_smul]
  congr 1
  have hsgn : ((sgn (m * (j + jv)) : ℤˣ) : ℤ) * ((sgn (m * jv) : ℤˣ) : ℤ)
      = ((sgn (m * j) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_dslot2_deg]
  linear_combination ((sgn (e * j) : ℤˣ) : ℤ) * s' * hsgn

/-- The associativity recast of the total coefficient algebra used by
`comp_right`. -/
private theorem right_recast_eq : a + b + c + d = a + (b + c + d) := by
  rw [add_assoc, add_assoc, add_assoc]

/-- `GE2` transports the right action plainly, along the recast
`D_{a+b+c+d} ≅ D_{a+((b+c)+d)}` — conditional on `t₂`'s own
right-equivariance for it. -/
theorem comp_right {j : ZMod 2}
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht₂R : ∀ (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)),
      t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v
            (MulOpposite.op τ • w))
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)
            • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
            (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂
        (MulOpposite.op τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)
          • GE2 K Γ a b c d e t₂ ht₂
              (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w) := by
  have hL : GE2 K Γ a b c d e t₂ ht₂
      (MulOpposite.op τ • GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d u
            (MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)
              • t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier
                (FusionColumn (Γ.fuse a (b + c))) (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
    rw [GQ2.right_smul_mk, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v (MulOpposite.op τ • w), ht₂R]
  rw [hL, GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w, smul_comm
    (MulOpposite.op ((Γ.gaugeCast (right_recast_eq a b c d)).toAlgEquiv τ)),
    GQ3.right_smul_mk]

/-- `GE2` is homogeneous of `t₂`'s degree `e`. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₂deg : ∀ jj : ZMod 2,
      ∀ n ∈ relGrading (Γ.D (a + b + c)).carrier
          (FusionColumn.grading (Γ.fuse a (b + c))) (FusionColumn.grading (Γ.fuse (a + b + c) d)) jj,
        t₂ n ∈ GQ3Inner.grading K Γ a b c d (jj + e))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    {v : FusionColumn (Γ.fuse a (b + c))} (hv : v ∈ FusionColumn.grading (Γ.fuse a (b + c)) jv)
    {w : FusionColumn (Γ.fuse (a + b + c) d)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) jw) :
    GE2 K Γ a b c d e t₂ ht₂ (GQ2.mk K Γ a b c d (GBR.mk Γ a b c u v) w)
      ∈ GQ3.grading K Γ a b c d (j + (jv + jw + e)) := by
  rw [GE2_mk_of_mem' K Γ a b c d e t₂ ht₂ hu v w]
  refine zsmul_mem ?_ _
  exact GQ3.mk_mem_grading K Γ a b c d hu
    (ht₂deg (jv + jw) _ (mk_mem_relGrading _ _ hv hw))

end GE2

/-! ### The third pentagon edge -/

namespace GE3

variable (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
variable (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
  t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)

/-- `GE3_mk`, restated through the synonym-valued `mk`s of `GQ3`, `GBR`
(the spelling of `GQ3Inner`) and `GQ4`. -/
private theorem GE3_mk' (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃
        (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = GQ4.mk K Γ a b c d (t₃ (GBL.mk Γ b c d u v)) w :=
  GE3_mk K Γ a b c d t₃ ht₃ u v w

private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

private theorem zmod2_aslot_deg : ∀ e k j jv : ZMod 2,
    e * k + k * (j + jv + e) = k * (j + jv) := by decide

/-- `GQ3Inner` is a `def` bridging to `GBR Γ a (b+c) d`, so its slot
instances are *separate* (though defeq) registrations from `GBR`'s own —
these three private bridges restate the needed `GBR` slot laws directly at
`GQ3Inner`'s own instance, by `exact` (full defeq checking). -/
private theorem GQ3Inner_dslot_smul (τ : (Γ.D d).carrier)
    (v : FusionColumn (Γ.fuse (b + c) d)) (w : FusionColumn (Γ.fuse a (b + c + d))) :
    τ • (GBR.mk Γ a (b + c) d v w : GQ3Inner K Γ a b c d)
      = (GBR.mk Γ a (b + c) d (τ • v) w : GQ3Inner K Γ a b c d) :=
  GBR.cslot_smul_mk Γ a (b + c) d τ v w

private theorem GQ3Inner_aslot_smul_of_mem {jv k : ZMod 2}
    {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    {v : FusionColumn (Γ.fuse (b + c) d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    x • (GBR.mk Γ a (b + c) d v w : GQ3Inner K Γ a b c d)
      = ((sgn (k * jv) : ℤˣ) : ℤ) •
          (GBR.mk Γ a (b + c) d v (x • w) : GQ3Inner K Γ a b c d) :=
  GBR.aslot_smul_mk_of_mem Γ a (b + c) d hx hv w

private theorem GQ3Inner_right_smul
    (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (v : FusionColumn (Γ.fuse (b + c) d)) (w : FusionColumn (Γ.fuse a (b + c + d))) :
    τ • (GBR.mk Γ a (b + c) d v w : GQ3Inner K Γ a b c d)
      = (GBR.mk Γ a (b + c) d v (τ • w) : GQ3Inner K Γ a b c d) :=
  GBR.right_smul_mk Γ a (b + c) d τ v w

/-- `GE3` transports the `b`-slot up to `t₃`'s own equivariance scalar `s`
for it — `T_b` is a *direct* outer slot of both `GBL(b,c,d)` and
`GBR(b,c,d)`, and `GE3`'s generator formula carries no sign at all, so the
transport is exactly `t₃`'s own scalar. -/
theorem comp_bslot {s : ℤ} {y : (Γ.D b).carrier}
    (ht₃B : ∀ m : GBL Γ b c d, t₃ (y • m) = s • (y • t₃ m))
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃ (y • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = s • (y • GE3 K Γ a b c d t₃ ht₃
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))) := by
  rw [GQ3.bslot_smul_mk, GE3_mk' K Γ a b c d t₃ ht₃ (y • u) v w,
    GE3_mk' K Γ a b c d t₃ ht₃ u v w, ← GBL.aslot_smul_mk, ht₃B]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← GQ4.bslot_smul_mk]

/-- `GE3` transports the `c`-slot up to `t₃`'s own equivariance scalar `s`
for it — exactly parallel to `comp_bslot`. -/
theorem comp_cslot {s : ℤ} {z : (Γ.D c).carrier}
    (ht₃C : ∀ m : GBL Γ b c d, t₃ (z • m) = s • (z • t₃ m))
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃ (z • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = s • (z • GE3 K Γ a b c d t₃ ht₃
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))) := by
  rw [GQ3.cslot_smul_mk, GE3_mk' K Γ a b c d t₃ ht₃ (z • u) v w,
    GE3_mk' K Γ a b c d t₃ ht₃ u v w, ← GBL.bslot_smul_mk, ht₃C]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← GQ4.cslot_smul_mk]

/-- `GE3` transports the `d`-slot up to `t₃`'s own equivariance scalar `s`
for it — the mid-of-mid sign of `GQ3` and `GBL`'s own signed middle-slot law
for `T_d` (both keyed to the same `(m,j)`) cancel exactly. -/
theorem comp_dslot {s : ℤ} {j m : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₃D : ∀ n : GBL Γ b c d, t₃ (τ • n) = s • (τ • t₃ n))
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse (b + c) d)) (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃ (τ • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = s • (τ • GE3 K Γ a b c d t₃ ht₃
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))) := by
  have hv' : GBL.mk Γ b c d u (τ • v)
      = ((sgn (m * j) : ℤˣ) : ℤ) • (τ • GBL.mk Γ b c d u v) := by
    rw [GBL.cslot_smul_mk_of_mem Γ b c d hτ hu, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have step1 : τ • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)
      = ((sgn (m * j) : ℤˣ) : ℤ) •
          GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d (τ • v) w) := by
    rw [GQ3.dslot_smul_mk_of_mem K Γ a b c d hτ hu]
    exact congrArg (fun z => ((sgn (m * j) : ℤˣ) : ℤ) • GQ3.mk K Γ a b c d u z)
      (GQ3Inner_dslot_smul K Γ a b c d τ v w)
  rw [step1, map_zsmul, GE3_mk' K Γ a b c d t₃ ht₃ u (τ • v) w, hv']
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [ht₃D]
  simp only [map_zsmul, LinearMap.smul_apply]
  rw [← GQ4.dslot_smul_mk, GE3_mk' K Γ a b c d t₃ ht₃ u v w, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]

/-- `GE3` transports the `a`-slot up to the amplification's own sign
`(-1)^{e|x|}` — the *spectator* slot: `GBL(b,c,d)`/`GBR(b,c,d)` carry no
`T_a`-action at all. -/
theorem comp_aslot {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e))
    {k j jv : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    {u : FusionColumn (Γ.fuse b c)} (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    {v : FusionColumn (Γ.fuse (b + c) d)} (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃ (x • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (x • GE3 K Γ a b c d t₃ ht₃
            (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))) := by
  have hL : GE3 K Γ a b c d t₃ ht₃ (x • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = ((sgn (k * (j + jv)) : ℤˣ) : ℤ) •
          GQ4.mk K Γ a b c d (t₃ (GBL.mk Γ b c d u v)) (x • w) := by
    have step1 : x • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)
        = ((sgn (k * j) : ℤˣ) : ℤ) •
            (((sgn (k * jv) : ℤˣ) : ℤ) •
              GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v (x • w))) := by
      have hA := GQ3.aslot_smul_mk_of_mem K Γ a b c d hx hu
        (GBR.mk Γ a (b + c) d v w)
      have hC := congrArg (fun z => GQ3.mk K Γ a b c d u z)
        (GQ3Inner_aslot_smul_of_mem K Γ a b c d hx hv w)
      have hD := map_zsmul (GQ3.mk K Γ a b c d u) ((sgn (k * jv) : ℤˣ) : ℤ)
        (GBR.mk Γ a (b + c) d v (x • w))
      exact hA.trans (congrArg (fun z => ((sgn (k * j) : ℤˣ) : ℤ) • z) (hC.trans hD))
    rw [step1, smul_smul, ← Units.val_mul, ← sgn_add, ← mul_add, map_zsmul,
      GE3_mk' K Γ a b c d t₃ ht₃ u v (x • w)]
  rw [hL, GE3_mk' K Γ a b c d t₃ ht₃ u v w,
    GQ4.aslot_smul_mk_of_mem K Γ a b c d hx
      (ht₃deg (j + jv) _ (GBL.mk_mem_grading Γ b c d hu hv))]
  simp only [smul_smul]
  congr 1
  rw [← Units.val_mul, ← sgn_add]
  congr 1
  exact congrArg sgn (zmod2_aslot_deg e k j jv).symm

/-- `GE3` transports the right action plainly — `GQ3`'s and `GQ4`'s outer
right-coefficient towers are both literally `D_{a+(b+c+d)}`. -/
theorem comp_right (τ : ((Γ.D (a + (b + c + d))).carrier)ᵐᵒᵖ)
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃ (τ • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      = τ • GE3 K Γ a b c d t₃ ht₃
          (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)) := by
  have step1 : τ • GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w)
      = GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v (τ • w)) := by
    rw [GQ3.right_smul_mk]
    exact congrArg (fun z => GQ3.mk K Γ a b c d u z) (GQ3Inner_right_smul K Γ a b c d τ v w)
  rw [step1, GE3_mk' K Γ a b c d t₃ ht₃ u v (τ • w),
    GE3_mk' K Γ a b c d t₃ ht₃ u v w, GQ4.right_smul_mk]

/-- `GE3` is homogeneous of `t₃`'s degree `e`. -/
theorem mem_grading {e : ZMod 2}
    (ht₃deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ b c d j',
      t₃ n ∈ GBR.grading Γ b c d (j' + e))
    {j jv jw : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    {v : FusionColumn (Γ.fuse (b + c) d)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse (b + c) d) jv)
    {w : FusionColumn (Γ.fuse a (b + c + d))}
    (hw : w ∈ FusionColumn.grading (Γ.fuse a (b + c + d)) jw) :
    GE3 K Γ a b c d t₃ ht₃ (GQ3.mk K Γ a b c d u (GBR.mk Γ a (b + c) d v w))
      ∈ GQ4.grading K Γ a b c d (j + (jv + jw + e)) := by
  rw [GE3_mk' K Γ a b c d t₃ ht₃ u v w]
  have h := GQ4.mk_mem_grading K Γ a b c d
    (ht₃deg (j + jv) _ (GBL.mk_mem_grading Γ b c d hu hv)) hw
  rwa [show (j + jv + e) + jw = j + (jv + jw + e) from by ring] at h

end GE3

/-! ### The fourth pentagon edge -/

namespace GE4

variable (e : ZMod 2) (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
variable (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
  x ∈ (Γ.D (a + b)).grading i →
  ∀ n : GBL Γ (a + b) c d,
    t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))

/-- `GE4_mk_of_mem`, restated through the synonym-valued `mk`s of `GQ1` and
`GQ5`. -/
private theorem GE4_mk_of_mem' {j : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄ (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b c d u (t₄ (GBL.mk Γ (a + b) c d v w)) :=
  GE4_mk_of_mem K Γ a b c d e t₄ ht₄ hu v w

private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

private theorem zmod2_dslot_deg : ∀ m j jv : ZMod 2,
    m * (j + jv) + m * jv + m * j = 0 := by decide

/-- `GE4` transports the `a`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot: `GBL(a+b,c,d)`/`GBR(a+b,c,d)` carry no
`T_a`-action at all (only the *combined* `(a+b)`-slot does). -/
theorem comp_aslot {k j : ZMod 2} {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄ (x • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (x • GE4 K Γ a b c d e t₄ ht₄
            (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)) := by
  have hL : GE4 K Γ a b c d e t₄ ht₄ (x • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * (k + j)) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b c d (x • u) (t₄ (GBL.mk Γ (a + b) c d v w)) := by
    rw [GQ1.aslot_smul_mk, GBL.aslot_smul_mk]
    exact GE4_mk_of_mem' K Γ a b c d e t₄ ht₄
      ((vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hx hu) v w
  rw [hL, GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w, smul_comm x, GQ5.aslot_smul_mk,
    smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `GE4` transports the `b`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot, exactly parallel to `comp_aslot`. -/
theorem comp_bslot {k j : ZMod 2} {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄ (y • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (y • GE4 K Γ a b c d e t₄ ht₄
            (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)) := by
  have hL : GE4 K Γ a b c d e t₄ ht₄ (y • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * (k + j)) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b c d (y • u) (t₄ (GBL.mk Γ (a + b) c d v w)) := by
    rw [GQ1.bslot_smul_mk, GBL.bslot_smul_mk]
    exact GE4_mk_of_mem' K Γ a b c d e t₄ ht₄
      ((vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hy hu) v w
  rw [hL, GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w, smul_comm y, GQ5.bslot_smul_mk,
    smul_smul, ← Units.val_mul, ← sgn_add, mul_add]

/-- `GE4` transports the `c`-slot up to `t₄`'s own equivariance scalar `s`
for it — the two Koszul signs cancel exactly. -/
theorem comp_cslot {s : ℤ} {k j : ZMod 2}
    {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k)
    (ht₄C : ∀ n : GBL Γ (a + b) c d, t₄ (z • n) = s • (z • t₄ n))
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄ (z • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = s • (z • GE4 K Γ a b c d e t₄ ht₄
          (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)) := by
  have h1 : z • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          GQ1.mk K Γ a b c d (GBL.mk Γ a b c u (z • v)) w := by
    rw [GQ1.cslot_smul_mk, GBL.cslot_smul_mk_of_mem Γ a b c hz hu]
    simp only [map_zsmul, LinearMap.smul_apply]
  have h2 : GE4 K Γ a b c d e t₄ ht₄
      (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u (z • v)) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          (s • GQ5.mk K Γ a b c d u (z • t₄ (GBL.mk Γ (a + b) c d v w))) := by
    rw [GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu (z • v) w, ← GBL.bslot_smul_mk, ht₄C]
    simp only [map_zsmul]
  have h3 : GQ5.mk K Γ a b c d u (z • t₄ (GBL.mk Γ (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (z • GQ5.mk K Γ a b c d u (t₄ (GBL.mk Γ (a + b) c d v w))) := by
    rw [GQ5.cslot_smul_mk_of_mem K Γ a b c d hz hu, smul_smul, ← Units.val_mul, ← sgn_add,
      zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have hkey : ((sgn (k * j) : ℤˣ) : ℤ) * ((sgn (k * j) : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one]
  rw [h1, map_zsmul, h2, h3, GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w, smul_comm z]
  simp only [smul_smul]
  congr 1
  linear_combination (s * ((sgn (e * j) : ℤˣ) : ℤ)) * hkey

/-- `GE4` transports the `d`-slot up to `t₄`'s own equivariance scalar `s'`
for it — three Koszul signs combine to `1` and cancel exactly. -/
theorem comp_dslot {s' : ℤ} {m j jv : ZMod 2}
    {τ : (Γ.D d).carrier}
    (hτ : τ ∈ (Γ.D d).grading m)
    (ht₄D : ∀ n : GBL Γ (a + b) c d, t₄ (τ • n) = s' • (τ • t₄ n))
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄ (τ • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = s' • (τ • GE4 K Γ a b c d e t₄ ht₄
          (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)) := by
  have h1 : τ • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w
      = ((sgn (m * (j + jv)) : ℤˣ) : ℤ) •
          GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) (τ • w) :=
    GQ1.dslot_smul_mk_of_mem K Γ a b c d hτ (GBL.mk_mem_grading Γ a b c hu hv) w
  have h2 : GBL.mk Γ (a + b) c d v (τ • w)
      = ((sgn (m * jv) : ℤˣ) : ℤ) • (τ • GBL.mk Γ (a + b) c d v w) := by
    rw [GBL.cslot_smul_mk_of_mem Γ (a + b) c d hτ hv, smul_smul, ← Units.val_mul,
      ← sgn_add, zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have h3 : GQ5.mk K Γ a b c d u (τ • t₄ (GBL.mk Γ (a + b) c d v w))
      = ((sgn (m * j) : ℤˣ) : ℤ) •
          (τ • GQ5.mk K Γ a b c d u (t₄ (GBL.mk Γ (a + b) c d v w))) := by
    rw [GQ5.dslot_smul_mk_of_mem K Γ a b c d hτ hu, smul_smul, ← Units.val_mul, ← sgn_add,
      zmod2_dbl, sgn_zero, Units.val_one, one_smul]
  have h4 : GE4 K Γ a b c d e t₄ ht₄
      (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) (τ • w))
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          (((sgn (m * jv) : ℤˣ) : ℤ) •
            (s' • GQ5.mk K Γ a b c d u (τ • t₄ (GBL.mk Γ (a + b) c d v w)))) := by
    rw [GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v (τ • w), h2]
    simp only [map_zsmul]
    rw [ht₄D]
    simp only [map_zsmul]
  have hkey3 : ((sgn (m * (j + jv)) : ℤˣ) : ℤ) * ((sgn (m * jv) : ℤˣ) : ℤ) *
      ((sgn (m * j) : ℤˣ) : ℤ) = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add, zmod2_dslot_deg,
      sgn_zero, Units.val_one]
  rw [h1, map_zsmul, h4, h3, GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w, smul_comm τ]
  simp only [smul_smul]
  congr 1
  linear_combination (s' * ((sgn (e * j) : ℤˣ) : ℤ)) * hkey3

/-- The associativity recast of the total coefficient algebra used by
`comp_right`. -/
private theorem right_recast_eq4 : a + b + c + d = a + b + (c + d) := by
  rw [add_assoc]

/-- `GE4` transports the right action along the recast
`D_{a+b+c+d} ≅ D_{a+b+(c+d)}` — conditional on `t₄`'s own right-equivariance
for it. -/
theorem comp_right {j : ZMod 2}
    (τ : (Γ.D (a + b + c + d)).carrier)
    (ht₄R : ∀ n : GBL Γ (a + b) c d,
      t₄ (MulOpposite.op τ • n)
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ) • t₄ n)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄
        (MulOpposite.op τ • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ)
          • GE4 K Γ a b c d e t₄ ht₄
              (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w) := by
  have hL : GE4 K Γ a b c d e t₄ ht₄
      (MulOpposite.op τ • GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          GQ5.mk K Γ a b c d u
            (MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ)
              • t₄ (GBL.mk Γ (a + b) c d v w)) := by
    rw [GQ1.right_smul_mk,
      GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v (MulOpposite.op τ • w),
      ← GBL.right_smul_mk, ht₄R]
  rw [hL, GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w, smul_comm
    (MulOpposite.op ((Γ.gaugeCast (right_recast_eq4 a b c d)).toAlgEquiv τ)),
    GQ5.right_smul_mk]

/-- `GE4` is homogeneous of `t₄`'s degree `e`. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₄deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ (a + b) c d j',
      t₄ n ∈ GBR.grading Γ (a + b) c d (j' + e))
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    {v : FusionColumn (Γ.fuse (a + b) c)} (hv : v ∈ FusionColumn.grading (Γ.fuse (a + b) c) jv)
    {w : FusionColumn (Γ.fuse (a + b + c) d)}
    (hw : w ∈ FusionColumn.grading (Γ.fuse (a + b + c) d) jw) :
    GE4 K Γ a b c d e t₄ ht₄ (GQ1.mk K Γ a b c d (GBL.mk Γ a b c u v) w)
      ∈ GQ5.grading K Γ a b c d (j + (jv + jw + e)) := by
  rw [GE4_mk_of_mem' K Γ a b c d e t₄ ht₄ hu v w]
  refine zsmul_mem ?_ _
  exact GQ5.mk_mem_grading K Γ a b c d hu
    (ht₄deg (jv + jw) _ (GBL.mk_mem_grading Γ (a + b) c d hv hw))

end GE4

/-! ### The fifth pentagon edge -/

namespace GE5

variable (e : ZMod 2) (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
variable (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
  z ∈ (Γ.D (c + d)).grading i →
  ∀ n : GBL Γ a b (c + d),
    t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))

/-- `GE5_mk_of_mem`, restated through the synonym-valued `mk`s of `GQ5` and
`GQ4r`. -/
private theorem GE5_mk_of_mem' {i j : ZMod 2} {v : FusionColumn (Γ.fuse c d)}
    {u : FusionColumn (Γ.fuse a b)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅ (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b c d v (t₅ (GBL.mk Γ a b (c + d) u w)) :=
  GE5_mk_of_mem K Γ a b c d e t₅ ht₅ hv hu w

private theorem zmod2_dbl : ∀ i j : ZMod 2, i * j + i * j = 0 := by decide

private theorem zmod2_ab_deg : ∀ i e k j : ZMod 2,
    i * (e + (k + j)) + k * i = i * (e + j) := by decide

private theorem zmod2_cd_deg : ∀ e k j i : ZMod 2,
    k * j + (k + i) * (e + j) = e * k + i * (e + j) := by decide

/-- `GE5` transports the `a`-slot up to `t₅`'s own equivariance scalar `s`
for it — the swap/amplification sign and `GQ4r`'s own mid-of-mid sign
combine to cancel the base formula's own sign exactly. -/
theorem comp_aslot {s : ℤ} {k j i : ZMod 2}
    {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (ht₅A : ∀ n : GBL Γ a b (c + d), t₅ (x • n) = s • (x • t₅ n))
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅ (x • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = s • (x • GE5 K Γ a b c d e t₅ ht₅
          (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))) := by
  have h1 : x • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)
      = GQ5.mk K Γ a b c d (x • u) (GBR.mk Γ (a + b) c d v w) :=
    GQ5.aslot_smul_mk K Γ a b c d x u (GBR.mk Γ (a + b) c d v w)
  have hxu : x • u ∈ FusionColumn.grading (Γ.fuse a b) (k + j) :=
    (vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hx hu
  have h2 : GE5 K Γ a b c d e t₅ ht₅
      (GQ5.mk K Γ a b c d (x • u) (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) •
          (s • GQ4r.mk K Γ a b c d v (x • t₅ (GBL.mk Γ a b (c + d) u w))) := by
    rw [GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hxu w, ← GBL.aslot_smul_mk, ht₅A]
    simp only [map_zsmul]
  have h3 : GQ4r.mk K Γ a b c d v (x • t₅ (GBL.mk Γ a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (x • GQ4r.mk K Γ a b c d v (t₅ (GBL.mk Γ a b (c + d) u w))) := by
    rw [GQ4r.aslot_smul_mk_of_mem K Γ a b c d hx hv
        (t₅ (GBL.mk Γ a b (c + d) u w)),
      smul_smul, ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero,
      Units.val_one, one_smul]
  have hkey : ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) * ((sgn (k * i) : ℤˣ) : ℤ)
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_ab_deg]
  rw [h1, h2, h3, GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w, smul_comm x]
  simp only [smul_smul]
  congr 1
  linear_combination s * hkey

/-- `GE5` transports the `b`-slot up to `t₅`'s own equivariance scalar `s`
for it — exactly parallel to `comp_aslot`. -/
theorem comp_bslot {s : ℤ} {k j i : ZMod 2}
    {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    (ht₅B : ∀ n : GBL Γ a b (c + d), t₅ (y • n) = s • (y • t₅ n))
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅ (y • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = s • (y • GE5 K Γ a b c d e t₅ ht₅
          (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))) := by
  have h1 : y • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)
      = GQ5.mk K Γ a b c d (y • u) (GBR.mk Γ (a + b) c d v w) :=
    GQ5.bslot_smul_mk K Γ a b c d y u (GBR.mk Γ (a + b) c d v w)
  have hyu : y • u ∈ FusionColumn.grading (Γ.fuse a b) (k + j) :=
    (vadd_eq_add k j) ▸ SetLike.GradedSMul.smul_mem hy hu
  have h2 : GE5 K Γ a b c d e t₅ ht₅
      (GQ5.mk K Γ a b c d (y • u) (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) •
          (s • GQ4r.mk K Γ a b c d v (y • t₅ (GBL.mk Γ a b (c + d) u w))) := by
    rw [GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hyu w, ← GBL.bslot_smul_mk, ht₅B]
    simp only [map_zsmul]
  have h3 : GQ4r.mk K Γ a b c d v (y • t₅ (GBL.mk Γ a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          (y • GQ4r.mk K Γ a b c d v (t₅ (GBL.mk Γ a b (c + d) u w))) := by
    rw [GQ4r.bslot_smul_mk_of_mem K Γ a b c d hy hv
        (t₅ (GBL.mk Γ a b (c + d) u w)),
      smul_smul, ← Units.val_mul, ← sgn_add, zmod2_dbl, sgn_zero,
      Units.val_one, one_smul]
  have hkey : ((sgn (i * (e + (k + j))) : ℤˣ) : ℤ) * ((sgn (k * i) : ℤˣ) : ℤ)
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add, zmod2_ab_deg]
  rw [h1, h2, h3, GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w, smul_comm y]
  simp only [smul_smul]
  congr 1
  linear_combination s * hkey

/-- `GE5` transports the `c`-slot up to the amplification's own sign
`(-1)^{ek}` — the *spectator* slot with respect to `t₅`. -/
theorem comp_cslot {k j i : ZMod 2} {z : (Γ.D c).carrier}
    (hz : z ∈ (Γ.D c).grading k)
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅ (z • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (z • GE5 K Γ a b c d e t₅ ht₅
            (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))) := by
  have hzv : z • v ∈ FusionColumn.grading (Γ.fuse c d) (k + i) :=
    (vadd_eq_add k i) ▸ SetLike.GradedSMul.smul_mem hz hv
  have hL : GE5 K Γ a b c d e t₅ ht₅
      (z • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (((sgn ((k + i) * (e + j)) : ℤˣ) : ℤ) •
            (z • GQ4r.mk K Γ a b c d v (t₅ (GBL.mk Γ a b (c + d) u w)))) := by
    rw [GQ5.cslot_smul_mk_of_mem K Γ a b c d hz hu, GBR.bslot_smul_mk, map_zsmul,
      GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hzv hu w, ← GQ4r.cslot_smul_mk]
  rw [hL, smul_smul, ← Units.val_mul, ← sgn_add,
    GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w, smul_comm z, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_cd_deg]

/-- `GE5` transports the `d`-slot up to the amplification's own sign
`(-1)^{ek}` — exactly parallel to `comp_cslot`. -/
theorem comp_dslot {k j i : ZMod 2} {t : (Γ.D d).carrier}
    (ht : t ∈ (Γ.D d).grading k)
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅ (t • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (e * k) : ℤˣ) : ℤ) •
          (t • GE5 K Γ a b c d e t₅ ht₅
            (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))) := by
  have htv : t • v ∈ FusionColumn.grading (Γ.fuse c d) (k + i) :=
    (vadd_eq_add k i) ▸ SetLike.GradedSMul.smul_mem ht hv
  have hL : GE5 K Γ a b c d e t₅ ht₅
      (t • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          (((sgn ((k + i) * (e + j)) : ℤˣ) : ℤ) •
            (t • GQ4r.mk K Γ a b c d v (t₅ (GBL.mk Γ a b (c + d) u w)))) := by
    rw [GQ5.dslot_smul_mk_of_mem K Γ a b c d ht hu, GBR.cslot_smul_mk, map_zsmul,
      GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ htv hu w, ← GQ4r.dslot_smul_mk]
  rw [hL, smul_smul, ← Units.val_mul, ← sgn_add,
    GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w, smul_comm t, smul_smul,
    ← Units.val_mul, ← sgn_add, zmod2_cd_deg]

/-- The associativity recast of the total coefficient algebra used by
`comp_right`. -/
private theorem right_recast_eq5 : a + b + (c + d) = a + (b + (c + d)) := by
  rw [add_assoc]

/-- `GE5` transports the right action along the recast
`D_{a+b+(c+d)} ≅ D_{a+(b+(c+d))}` — conditional on `t₅`'s own
right-equivariance for it. -/
theorem comp_right {i j : ZMod 2}
    (τ : (Γ.D (a + b + (c + d))).carrier)
    (ht₅R : ∀ n : GBL Γ a b (c + d),
      t₅ (MulOpposite.op τ • n)
        = MulOpposite.op ((Γ.gaugeCast (right_recast_eq5 a b c d)).toAlgEquiv τ) • t₅ n)
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅
        (MulOpposite.op τ • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = MulOpposite.op ((Γ.gaugeCast (right_recast_eq5 a b c d)).toAlgEquiv τ)
          • GE5 K Γ a b c d e t₅ ht₅
              (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w)) := by
  have hL : GE5 K Γ a b c d e t₅ ht₅
      (MulOpposite.op τ • GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b c d v
            (MulOpposite.op ((Γ.gaugeCast (right_recast_eq5 a b c d)).toAlgEquiv τ)
              • t₅ (GBL.mk Γ a b (c + d) u w)) := by
    rw [GQ5.right_smul_mk, GBR.right_smul_mk,
      GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu (MulOpposite.op τ • w),
      ← GBL.right_smul_mk, ht₅R]
  rw [hL, GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w, smul_comm
    (MulOpposite.op ((Γ.gaugeCast (right_recast_eq5 a b c d)).toAlgEquiv τ)), GQ4r.right_smul_mk]

/-- `GE5` is homogeneous of `t₅`'s degree `e`. -/
theorem mem_grading {j jv jw : ZMod 2}
    (ht₅deg : ∀ j' : ZMod 2, ∀ n ∈ GBL.grading Γ a b (c + d) j',
      t₅ n ∈ GBR.grading Γ a b (c + d) (j' + e))
    {u : FusionColumn (Γ.fuse a b)} (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) jv)
    {w : FusionColumn (Γ.fuse (a + b) (c + d))}
    (hw : w ∈ FusionColumn.grading (Γ.fuse (a + b) (c + d)) jw) :
    GE5 K Γ a b c d e t₅ ht₅ (GQ5.mk K Γ a b c d u (GBR.mk Γ (a + b) c d v w))
      ∈ GQ4r.grading K Γ a b c d (j + (jv + jw + e)) := by
  rw [GE5_mk_of_mem' K Γ a b c d e t₅ ht₅ hv hu w]
  refine zsmul_mem ?_ _
  have h := GQ4r.mk_mem_grading K Γ a b c d hv
    (ht₅deg (j + jw) _ (GBL.mk_mem_grading Γ a b (c + d) hu hw))
  rwa [show jv + (j + jw + e) = j + (jv + jw + e) from by ring] at h

end GE5

/-! ### Transport of `gq4Close`

`gq4Close`'s two legs (`gq4lAssoc`, all balancings canonical; `gq4Recast`,
identity on the `GBR(b,c,d)`-factor and the column cast on the coefficient
factor) are both sign-free, so every transport law below is a **clean
equivariance** `gq4Close (ξ • g) = ξ • gq4Close g`, unconditionally. Two more
cast-compatibility lemmas for `fusionColumnCast` are added alongside
`Pentagon.lean`'s own two (`fusionColumnCast_symm_rslot`,
`fusionColumnCast_symm_symm_rslot`). -/

/-- The column cast leaves the untouched first-index slot action alone — a
`subst`-`refl` fact, mirroring `fusionColumnCast_symm_rslot`. -/
theorem fusionColumnCast_symm_lslot {x y : G} (h : x = y)
    (t : (Γ.D a).carrier) (w : FusionColumn (Γ.fuse a y)) :
    fusionColumnCast K Γ a h.symm (t • w) = t • fusionColumnCast K Γ a h.symm w := by
  subst h
  rfl

/-- The column cast intertwines the *natural coefficient* action along the
induced tower cast of the total sum — a `subst`-`refl` fact. -/
theorem fusionColumnCast_symm_coeff {x y : G} (h : x = y)
    (τ : (Γ.D (a + y)).carrier) (v : FusionColumn (Γ.fuse a y)) :
    fusionColumnCast K Γ a h.symm (MulOpposite.op τ • v)
      = MulOpposite.op ((Γ.gaugeCast (congrArg (a + ·) h)).toAlgEquiv.symm τ)
          • fusionColumnCast K Γ a h.symm v := by
  subst h
  rfl

/-- The column cast preserves the descended grading — a `subst`-`refl`
fact. -/
theorem fusionColumnCast_symm_mem_grading {x y : G} (h : x = y) {j : ZMod 2}
    {w : FusionColumn (Γ.fuse a y)} (hw : w ∈ FusionColumn.grading (Γ.fuse a y) j) :
    fusionColumnCast K Γ a h.symm w ∈ FusionColumn.grading (Γ.fuse a x) j := by
  subst h
  exact hw

namespace GQ4Close

/-- `gq4Close_mk`, restated through the synonym-valued `mk`s of `GQ4r`,
`GBR` and `GQ4`. -/
private theorem gq4Close_mk' (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = GQ4.mk K Γ a b c d (GBR.mk Γ b c d v u)
          (fusionColumnCast K Γ a (add_assoc b c d).symm w) :=
  gq4Close_mk K Γ a b c d v u w

/-- **`gq4Close` transports the `a`-slot**, unconditionally and sign-free. -/
theorem comp_aslot {i j k : ZMod 2}
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse b (c + d))} (hu : u ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    {x : (Γ.D a).carrier}
    (hx : x ∈ (Γ.D a).grading k)
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4Close K Γ a b c d (x • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = x • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) := by
  have hL : x • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)
      = ((sgn (k * (i + j)) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u (x • w)) := by
    rw [GQ4r.aslot_smul_mk_of_mem K Γ a b c d hx hv (GBR.mk Γ a b (c + d) u w),
      GBR.aslot_smul_mk_of_mem Γ a b (c + d) hx hu w, map_zsmul, smul_smul,
      ← Units.val_mul, ← sgn_add, ← mul_add]
  have hR : x • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = ((sgn (k * (i + j)) : ℤˣ) : ℤ) •
          gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u (x • w))) := by
    rw [gq4Close_mk', GQ4.aslot_smul_mk_of_mem K Γ a b c d hx
        (GBR.mk_mem_grading Γ b c d hv hu)
        (fusionColumnCast K Γ a (add_assoc b c d).symm w),
      ← fusionColumnCast_symm_lslot K Γ a (add_assoc b c d) x w, ← gq4Close_mk']
  rw [hL, map_zsmul, hR]

/-- **`gq4Close` transports the `b`-slot**, unconditionally and sign-free —
exactly parallel to `comp_aslot`. -/
theorem comp_bslot {i k : ZMod 2}
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {y : (Γ.D b).carrier}
    (hy : y ∈ (Γ.D b).grading k)
    (u : FusionColumn (Γ.fuse b (c + d))) (w : FusionColumn (Γ.fuse a (b + (c + d)))) :
    gq4Close K Γ a b c d (y • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = y • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) := by
  have hL : y • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) (y • u) w) := by
    rw [GQ4r.bslot_smul_mk_of_mem K Γ a b c d hy hv (GBR.mk Γ a b (c + d) u w),
      GBR.bslot_smul_mk Γ a b (c + d) y u w]
  have hR : y • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = ((sgn (k * i) : ℤˣ) : ℤ) •
          gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) (y • u) w)) := by
    rw [gq4Close_mk', GQ4.bslot_smul_mk K Γ a b c d y (GBR.mk Γ b c d v u)
        (fusionColumnCast K Γ a (add_assoc b c d).symm w),
      GBR.aslot_smul_mk_of_mem Γ b c d hy hv u]
    simp only [map_zsmul, LinearMap.smul_apply]
    rw [← gq4Close_mk']
  rw [hL, map_zsmul, hR]

/-- **`gq4Close` transports the `c`-slot**, fully directly (no sign, no
degree hypothesis anywhere). -/
theorem comp_cslot (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) (z : (Γ.D c).carrier) :
    gq4Close K Γ a b c d (z • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = z • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) := by
  rw [GQ4r.cslot_smul_mk, gq4Close_mk', gq4Close_mk', GQ4.cslot_smul_mk,
    GBR.bslot_smul_mk Γ b c d z v u]

/-- **`gq4Close` transports the `d`-slot**, fully directly — exactly parallel
to `comp_cslot`. -/
theorem comp_dslot (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d)))) (t : (Γ.D d).carrier) :
    gq4Close K Γ a b c d (t • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = t • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) := by
  rw [GQ4r.dslot_smul_mk, gq4Close_mk', gq4Close_mk', GQ4.dslot_smul_mk,
    GBR.cslot_smul_mk Γ b c d t v u]

/-- **`gq4Close` transports the right action** along the coefficient recast
`D_{a+(b+(c+d))} ≅ D_{a+(b+c+d)}` (keyed by the same associativity equality
`add_assoc b c d` used to build `gq4Close` itself) — no sign, sourced from
`fusionColumnCast_symm_coeff`. -/
theorem comp_right (v : FusionColumn (Γ.fuse c d)) (u : FusionColumn (Γ.fuse b (c + d)))
    (w : FusionColumn (Γ.fuse a (b + (c + d))))
    (τ : (Γ.D (a + (b + (c + d)))).carrier) :
    gq4Close K Γ a b c d
        (MulOpposite.op τ • GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      = MulOpposite.op ((Γ.gaugeCast (congrArg (a + ·) (add_assoc b c d))).toAlgEquiv.symm τ)
          • gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w)) := by
  rw [GQ4r.right_smul_mk, GBR.right_smul_mk, gq4Close_mk',
    fusionColumnCast_symm_coeff K Γ a (add_assoc b c d) τ w, ← GQ4.right_smul_mk,
    ← gq4Close_mk']

/-- **`gq4Close` is homogeneous of degree `0`** — it preserves the total
Koszul degree exactly. -/
theorem mem_grading {i j jw : ZMod 2}
    {v : FusionColumn (Γ.fuse c d)} (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    {u : FusionColumn (Γ.fuse b (c + d))} (hu : u ∈ FusionColumn.grading (Γ.fuse b (c + d)) j)
    {w : FusionColumn (Γ.fuse a (b + (c + d)))}
    (hw : w ∈ FusionColumn.grading (Γ.fuse a (b + (c + d))) jw) :
    gq4Close K Γ a b c d (GQ4r.mk K Γ a b c d v (GBR.mk Γ a b (c + d) u w))
      ∈ GQ4.grading K Γ a b c d (i + (j + jw)) := by
  rw [gq4Close_mk']
  have h := GQ4.mk_mem_grading K Γ a b c d (GBR.mk_mem_grading Γ b c d hv hu)
    (fusionColumnCast_symm_mem_grading K Γ a (add_assoc b c d) hw)
  rwa [show i + j + jw = i + (j + jw) from by ring] at h

end GQ4Close

end GaugeChi

end Superfusion
