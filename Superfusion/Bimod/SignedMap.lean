/-
Superfusion / Bimod / SignedMap

Milestone M8a-8c′-1b-ii (roadmap v3): **the signed second-slot
amplification** — the paper's `id ⊗ t` for a *homogeneous* intertwiner
`t` of parity `e`:

  `smap e g : M ⊗[A] N → M ⊗[A] N'`,
  `m ⊗ n ↦ (-1)^{e|m|} m ⊗ (g n)`.

For odd `g` the plain `RelTensor.map id g` is not defined (`g`
intertwines the balancing `A`-action only up to the Koszul sign), and
the sign against the first-slot parity is forced — the same
phenomenon as the signed middle action, and the same cure: the closed
bilinear form

  `m ⊗ (g n) - 2·e·(odd m) ⊗ (g n)`,

whose balancedness is exactly `g`'s signed equivariance.  At `e = 0`
this is the plain amplification (`smap_zero_eq_map`).
-/
import Superfusion.Bimod.MapEquivariance

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {N' : Type*} [AddCommGroup N'] [Module K N'] [Module A N']
variable (g : N →ₗ[K] N') (e : ZMod 2)

/-- The signed amplification in closed bilinear form:
`(m, n) ↦ m ⊗ (g n) - 2·e·(odd m) ⊗ (g n)`. -/
noncomputable def smapBilin :
    M →ₗ[K] N →ₗ[K] M ⊗[A;K] N' :=
  (RelTensor.mk K A M N').compl₁₂ LinearMap.id g
    - (2 * (e.val : ℤ)) •
      ((RelTensor.mk K A M N').compl₁₂ (modProj ℳ 1) g)

omit [Algebra K A] [Module A N] in
theorem smapBilin_apply (m : M) (n : N) :
    smapBilin (A := A) ℳ g e m n
      = RelTensor.mk K A M N' m (g n)
        - (2 * (e.val : ℤ)) •
          RelTensor.mk K A M N' (modProj ℳ 1 m) (g n) := rfl

omit [Algebra K A] [Module A N] in
/-- **The sign law**: on homogeneous `m ∈ ℳ j` the closed form is
`(-1)^{ej} m ⊗ (g n)`. -/
theorem smapBilin_of_mem {j : ZMod 2} {m : M} (hm : m ∈ ℳ j) (n : N) :
    smapBilin (A := A) ℳ g e m n
      = ((sgn (e * j) : ℤˣ) : ℤ) • RelTensor.mk K A M N' m (g n) := by
  rw [smapBilin_apply]
  rcases zmod2_cases e with he | he <;> rcases zmod2_cases j with hj | hj <;>
      subst he <;> subst hj
  · rw [show (((0 : ZMod 2).val : ℤ)) = 0 from rfl, mul_zero, zero_smul,
      sub_zero]
    simp
  · rw [show (((0 : ZMod 2).val : ℤ)) = 0 from rfl, mul_zero, zero_smul,
      sub_zero]
    simp
  · rw [modProj_of_mem_ne ℳ hm (by decide), map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem ℳ hm,
      show (((1 : ZMod 2).val : ℤ)) = 1 from rfl, mul_one,
      show (1 : ZMod 2) * 1 = 1 from by decide]
    simp only [sgn_one, units_sign_eq, Units.val_neg, Units.val_one,
      neg_smul, one_smul, two_smul]
    abel

/-- **Balancedness**: `g`'s signed equivariance makes the closed form
balanced. -/
theorem smapBalanced [GradedRightSMul 𝒜 ℳ]
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n)) :
    RelTensor.IsBalanced A (smapBilin (A := A) ℳ g e) := by
  intro a m n
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      rw [MulOpposite.op_zero, zero_smul, map_zero, LinearMap.zero_apply,
        zero_smul, map_zero]
  | add a a' ha ha' =>
      rw [MulOpposite.op_add, add_smul, map_add, LinearMap.add_apply,
        ha, ha', add_smul, map_add]
  | homogeneous xa =>
      induction m using DirectSum.Decomposition.inductionOn ℳ with
      | zero =>
          rw [smul_zero, map_zero, LinearMap.zero_apply,
            LinearMap.zero_apply]
      | add m m' hm hm' =>
          rw [smul_add, map_add, LinearMap.add_apply, hm, hm',
            ← LinearMap.add_apply, ← map_add]
      | homogeneous xm =>
          have sign_id : ∀ e i j : ZMod 2,
              e * (i + j) = e * j + e * i := by decide
          rw [smapBilin_of_mem ℳ g e
              (GradedRightSMul.smul_mem xa.2 xm.2) n,
            smapBilin_of_mem ℳ g e xm.2 ((xa : A) • n),
            RelTensor.mk_op_smul, hg xa.2 n, map_zsmul, smul_smul,
            ← Units.val_mul, ← sgn_add, sign_id]

section SMap

variable [GradedRightSMul 𝒜 ℳ]

/-- **The signed second-slot amplification**
`m ⊗ n ↦ (-1)^{e|m|} m ⊗ (g n)`. -/
noncomputable def smap
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n)) :
    (M ⊗[A;K] N) →ₗ[K] M ⊗[A;K] N' :=
  RelTensor.lift (smapBilin (A := A) ℳ g e) (smapBalanced 𝒜 ℳ g e hg)

theorem smap_mk
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    (m : M) (n : N) :
    smap 𝒜 ℳ g e hg (RelTensor.mk K A M N m n)
      = smapBilin (A := A) ℳ g e m n := by
  show RelTensor.lift (smapBilin (A := A) ℳ g e)
    (smapBalanced 𝒜 ℳ g e hg) (RelTensor.mk K A M N m n) = _
  rw [RelTensor.lift_mk]

/-- The sign law, descended. -/
theorem smap_mk_of_mem
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn (e * i) : ℤˣ) : ℤ) • (a • g n))
    {j : ZMod 2} {m : M} (hm : m ∈ ℳ j) (n : N) :
    smap 𝒜 ℳ g e hg (RelTensor.mk K A M N m n)
      = ((sgn (e * j) : ℤˣ) : ℤ) • RelTensor.mk K A M N' m (g n) := by
  rw [smap_mk, smapBilin_of_mem ℳ g e hm]

/-- At `e = 0` the signed amplification is the plain one. -/
theorem smap_zero_eq_map
    (hg : ∀ ⦃i : ZMod 2⦄ ⦃a : A⦄, a ∈ 𝒜 i → ∀ n : N,
      g (a • n) = ((sgn ((0 : ZMod 2) * i) : ℤˣ) : ℤ) • (a • g n))
    (hg' : ∀ (a : A) (n : N), g (a • n) = a • g n) :
    smap 𝒜 ℳ g 0 hg
      = RelTensor.map LinearMap.id g (fun _ _ => rfl) hg' := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [smap_mk, RelTensor.map_mk, smapBilin_apply,
    show (((0 : ZMod 2).val : ℤ)) = 0 from rfl, mul_zero, zero_smul,
    sub_zero]
  rfl

end SMap

end Bimod

end Superfusion
