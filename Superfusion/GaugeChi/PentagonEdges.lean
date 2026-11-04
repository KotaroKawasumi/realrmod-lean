/-
Superfusion / GaugeChi / PentagonEdges

Milestone M12-3 of the abstract `(p, χ)` arc (continued): **the five
quadruple pentagon edges** — the Γ-mirror of `Superfusion.Bimod.PentagonB`'s
`E1`–`E5` (`QuadRoutes`/`QuadEdge2b`/`QuadEdge3`/`QuadEdge4`/`QuadEdge5`),
built on the vertices and connecting isomorphisms of `GaugeChi.Pentagon`.

Each edge is parameterized over an ARBITRARY intertwiner datum with the
exact equivariance hypothesis its tower counterpart carries — no
`gInterSpace`-membership, no canonical instances (those come from
`exists_gIntertwiner` at the M12-4 membership round):

* `GE1 t`   `= RelTensor.map t id`, for a right-`D_{a+b+c}`-equivariant
  `t : GBL(a,b,c) → GBR(a,b,c)` — `GQ1 → GQ2`;
* `GE2 t₂`  `= (id ⊗_signed t₂) ∘ gq2Assoc`, for a spelled generator `t₂`
  of parity `e`, `D_{b+c}`-super-equivariant — `GQ2 → GQ3`;
* `GE3 t₃`  `= (t₃ ⊗ id) ∘ gq3Assoc⁻¹`, for a right-`D_{b+c+d}`-equivariant
  `t₃ : GBL(b,c,d) → GBR(b,c,d)` — `GQ3 → GQ4`;
* `GE4 t₄`  `= (id ⊗_signed t₄) ∘ gq1Assoc`, for a canonical triple
  intertwiner `t₄ : GBL(a+b,c,d) → GBR(a+b,c,d)` of parity `e`,
  `D_{a+b}`-super-equivariant — `GQ1 → GQ5`;
* `GE5 t₅`  `= (id ⊗_signed t₅) ∘ gq5Swap`, for a canonical triple
  intertwiner `t₅ : GBL(a,b,c+d) → GBR(a,b,c+d)` of parity `e`,
  `D_{c+d}`-super-equivariant — `GQ5 → GQ4r`.

Every generator formula and its sign is IDENTICAL to the tower's: the
signs come from the general `smap`/`RelTensor.map` machinery (M8a-8c′-1b),
not from `ZMod 8` — so the closed forms below are literal transcriptions
of `PentagonB.E1_mk`–`E5_mk_of_mem`.
-/
import Superfusion.GaugeChi.Pentagon
import Superfusion.Bimod.SignedMap

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

/-! ### The first pentagon edge -/

/-- **The first pentagon edge** `GE1 t = t ⊗ id : GQ1 → GQ2`, for a
right-equivariant `t : GBL(a,b,c) → GBR(a,b,c)`. -/
noncomputable def GE1 (t : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (ht : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t (MulOpposite.op τ • m) = MulOpposite.op τ • t m) :
    GQ1 K Γ a b c d →ₗ[K] GQ2 K Γ a b c d :=
  RelTensor.map t LinearMap.id ht (fun _ _ => rfl)

theorem GE1_mk (t : GBL Γ a b c →ₗ[K] GBR Γ a b c)
    (ht : ∀ (τ : (Γ.D (a + b + c)).carrier) (m : GBL Γ a b c),
      t (MulOpposite.op τ • m) = MulOpposite.op τ • t m)
    (u : GBL Γ a b c) (v : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE1 K Γ a b c d t ht
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) u v)
      = RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (t u) v := by
  show RelTensor.map t LinearMap.id ht (fun _ _ => rfl)
      (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
        (FusionColumn (Γ.fuse (a + b + c) d)) u v) = _
  rw [RelTensor.map_mk]
  rfl

/-! ### The second pentagon edge -/

/-- **The second pentagon edge** `GE2 t₂ = (id ⊗_signed t₂) ∘ gq2Assoc`,
for a spelled generator `t₂` of parity `e`, super-equivariant for the
`(b+c)`-slot. -/
noncomputable def GE2 (e : ZMod 2)
    (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n)) :
    GQ2 K Γ a b c d →ₗ[K] GQ3 K Γ a b c d :=
  (smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) t₂ e ht₂).comp
    (gq2Assoc K Γ a b c d).toLinearMap

/-- The generator formula of the second edge, on homogeneous first
slots. -/
theorem GE2_mk_of_mem (e : ZMod 2)
    (t₂ : GQ2rInner K Γ a b c d →ₗ[K] GQ3Inner K Γ a b c d)
    (ht₂ : ∀ ⦃i : ZMod 2⦄ ⦃y : (Γ.D (b + c)).carrier⦄,
      y ∈ (Γ.D (b + c)).grading i →
      ∀ n : GQ2rInner K Γ a b c d,
        t₂ (y • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (y • t₂ n))
    {j : ZMod 2} {u : FusionColumn (Γ.fuse b c)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse b c) j)
    (v : FusionColumn (Γ.fuse a (b + c))) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE2 K Γ a b c d e t₂ ht₂
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) u
            (t₂ (RelTensor.mk K (Γ.D (a + b + c)).carrier (FusionColumn (Γ.fuse a (b + c)))
              (FusionColumn (Γ.fuse (a + b + c) d)) v w)) := by
  show (smap (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c)) t₂ e ht₂)
      (gq2Assoc K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBR Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBR.mk Γ a b c u v) w)) = _
  rw [gq2Assoc_mk, smap_mk_of_mem (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
    t₂ e ht₂ hu]

/-! ### The third pentagon edge -/

/-- **The third pentagon edge** `GE3 t₃ = (t₃ ⊗ id) ∘ gq3Assoc⁻¹`, for a
right-equivariant `t₃ : GBL(b,c,d) → GBR(b,c,d)`. -/
noncomputable def GE3 (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m) :
    GQ3 K Γ a b c d →ₗ[K] GQ4 K Γ a b c d :=
  (RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl)).comp
    (gq3Assoc K Γ a b c d).symm.toLinearMap

theorem GE3_mk (t₃ : GBL Γ b c d →ₗ[K] GBR Γ b c d)
    (ht₃ : ∀ (τ : (Γ.D (b + c + d)).carrier) (m : GBL Γ b c d),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    (u : FusionColumn (Γ.fuse b c)) (v : FusionColumn (Γ.fuse (b + c) d))
    (w : FusionColumn (Γ.fuse a (b + c + d))) :
    GE3 K Γ a b c d t₃ ht₃
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
            (FusionColumn (Γ.fuse a (b + c + d))) v w))
      = RelTensor.mk K (Γ.D (b + c + d)).carrier (GBR Γ b c d)
          (FusionColumn (Γ.fuse a (b + c + d))) (t₃ (GBL.mk Γ b c d u v)) w := by
  show (RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl))
      ((gq3Assoc K Γ a b c d).symm
        (RelTensor.mk K (Γ.D (b + c)).carrier (FusionColumn (Γ.fuse b c)) (GQ3Inner K Γ a b c d) u
          (RelTensor.mk K (Γ.D (b + c + d)).carrier (FusionColumn (Γ.fuse (b + c) d))
            (FusionColumn (Γ.fuse a (b + c + d))) v w))) = _
  rw [← gq3Assoc_mk, LinearEquiv.symm_apply_apply, RelTensor.map_mk]
  rfl

/-! ### The fourth pentagon edge -/

/-- **The fourth pentagon edge** `GE4 t₄ = (id ⊗_signed t₄) ∘ gq1Assoc`,
for a canonical triple intertwiner `t₄ : GBL(a+b,c,d) → GBR(a+b,c,d)` of
parity `e`, super-equivariant for the `(a+b)`-slot. -/
noncomputable def GE4 (e : ZMod 2)
    (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i →
      ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n)) :
    GQ1 K Γ a b c d →ₗ[K] GQ5 K Γ a b c d :=
  (smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) t₄ e ht₄).comp
    (gq1Assoc K Γ a b c d).toLinearMap

/-- The generator formula of the fourth edge, on homogeneous first
slots. -/
theorem GE4_mk_of_mem (e : ZMod 2)
    (t₄ : GBL Γ (a + b) c d →ₗ[K] GBR Γ (a + b) c d)
    (ht₄ : ∀ ⦃i : ZMod 2⦄ ⦃x : (Γ.D (a + b)).carrier⦄,
      x ∈ (Γ.D (a + b)).grading i →
      ∀ n : GBL Γ (a + b) c d,
        t₄ (x • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (x • t₄ n))
    {j : ZMod 2} {u : FusionColumn (Γ.fuse a b)}
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (v : FusionColumn (Γ.fuse (a + b) c)) (w : FusionColumn (Γ.fuse (a + b + c) d)) :
    GE4 K Γ a b c d e t₄ ht₄
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)
      = ((sgn (e * j) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
            (t₄ (GBL.mk Γ (a + b) c d v w)) := by
  show (smap (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b)) t₄ e ht₄)
      (gq1Assoc K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b + c)).carrier (GBL Γ a b c)
          (FusionColumn (Γ.fuse (a + b + c) d)) (GBL.mk Γ a b c u v) w)) = _
  rw [gq1Assoc_mk, smap_mk_of_mem (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    t₄ e ht₄ hu]

/-! ### The fifth pentagon edge -/

/-- **The fifth pentagon edge** `GE5 t₅ = (id ⊗_signed t₅) ∘ gq5Swap`,
for a canonical triple intertwiner `t₅ : GBL(a,b,c+d) → GBR(a,b,c+d)` of
parity `e`, super-equivariant for the `(c+d)`-slot (the signed middle
action on the source, the outer slot action on the target). -/
noncomputable def GE5 (e : ZMod 2)
    (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i →
      ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n)) :
    GQ5 K Γ a b c d →ₗ[K] GQ4r K Γ a b c d :=
  (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) t₅ e ht₅).comp
    (gq5Swap K Γ a b c d).toLinearMap

/-- The generator formula of the fifth edge, on homogeneous first and
second slots: `u ⊗ (v ⊗ w) ↦ (-1)^{|v|(e+|u|)} v ⊗ t₅(u ⊗ w)`. -/
theorem GE5_mk_of_mem (e : ZMod 2)
    (t₅ : GBL Γ a b (c + d) →ₗ[K] GBR Γ a b (c + d))
    (ht₅ : ∀ ⦃i : ZMod 2⦄ ⦃z : (Γ.D (c + d)).carrier⦄,
      z ∈ (Γ.D (c + d)).grading i →
      ∀ n : GBL Γ a b (c + d),
        t₅ (z • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (z • t₅ n))
    {i j : ZMod 2} {v : FusionColumn (Γ.fuse c d)} {u : FusionColumn (Γ.fuse a b)}
    (hv : v ∈ FusionColumn.grading (Γ.fuse c d) i)
    (hu : u ∈ FusionColumn.grading (Γ.fuse a b) j)
    (w : FusionColumn (Γ.fuse (a + b) (c + d))) :
    GE5 K Γ a b c d e t₅ ht₅
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          (GBR.mk Γ (a + b) c d v w))
      = ((sgn (i * (e + j)) : ℤˣ) : ℤ) •
          RelTensor.mk K (Γ.D (c + d)).carrier (FusionColumn (Γ.fuse c d)) (GBR Γ a b (c + d)) v
            (t₅ (GBL.mk Γ a b (c + d) u w)) := by
  show (smap (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) t₅ e ht₅)
      (gq5Swap K Γ a b c d
        (RelTensor.mk K (Γ.D (a + b)).carrier (FusionColumn (Γ.fuse a b)) (GBR Γ (a + b) c d) u
          (GBR.mk Γ (a + b) c d v w))) = _
  have sign_id : ∀ e i j : ZMod 2, i * j + e * i = i * (e + j) := by decide
  rw [gq5Swap_mk_of_mem K Γ a b c d hv hu w, map_zsmul,
    smap_mk_of_mem (Γ.D (c + d)).grading (FusionColumn.grading (Γ.fuse c d)) t₅ e ht₅ hv,
    smul_smul, ← Units.val_mul, ← sgn_add, sign_id]

end GaugeChi

end Superfusion
