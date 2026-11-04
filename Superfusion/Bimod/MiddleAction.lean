/-
Superfusion / Bimod / MiddleAction

Milestone M8a-7a: **the Koszul-signed middle action** — the sign
convention of the paper's `B_L` (§4.1 / handoff):

  `(x ⊗ y ⊗ z) · (u ⊗ v) = (-1)^{|z||u|} ((x ⊗ y) u) ⊗ ((1 ⊗ z) v)`.

Setting: `N` carries, besides the left `A`-action balancing
`M ⊗[A] N`, a second graded left `C`-action which **supercommutes**
with the `A`-action (`SuperCommSMul`: for homogeneous `a`, `c`,
`a • (c • n) = (-1)^{|a||c|} c • (a • n)` — in `B_L`, `A = D_{ab}`
and `C = D_c` act through the two slots of `D_{ab} ⊗̂ D_c`).  Then

  `c • (m ⊗ n) = (-1)^{|c||m|} m ⊗ (c • n)`

is well defined on `M ⊗[A] N`: as everywhere in this project the sign
has the closed bilinear form (M3's trick)

  `midBilin c (m, n) = m ⊗ (c•n) - 2 (odd m) ⊗ ((odd c)•n)`,

whose balancedness is exactly the supercommutation.  The Koszul sign
consumes the parity of `m` only, so `c ↦ midEnd c` is plainly
multiplicative (no super-opposite needed); the algebra-map packaging
and the `(ℬ ᵍ⊗ 𝒞)`-module assembly are the next milestone.
-/
import Superfusion.Bimod.OuterActions

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
variable {C : Type*} [Ring C] [Algebra K C]
variable (𝒞 : ZMod 2 → Submodule K C) [GradedAlgebra 𝒞]
variable [Module C N] [IsScalarTower K C N]

/-- Two left actions on `N` **supercommute**: homogeneous elements
commute up to the Koszul sign.  (In `B_L` this is the ᵍ⊗-commutation
of the two slots of `D_{ab} ⊗̂ D_c` acting on `C_{ab,c}`.) -/
def SuperCommSMul (N : Type*) [AddCommGroup N] [SMul A N] [SMul C N] :
    Prop :=
  ∀ ⦃i k : ZMod 2⦄ ⦃a : A⦄ ⦃c : C⦄, a ∈ 𝒜 i → c ∈ 𝒞 k → ∀ n : N,
    a • (c • n) = ((sgn (i * k) : ℤˣ) : ℤ) • (c • (a • n))

private theorem zmod2_superCommSMul_symm :
    ∀ i k : ZMod 2, i * k + k * i = 0 := by
  decide

omit [Module K N] [IsScalarTower K C N]
  [GradedAlgebra 𝒜] [GradedAlgebra 𝒞] in
/-- Supercommutation is symmetric in the two graded actions. -/
theorem superCommSMul_symm (h : SuperCommSMul 𝒜 𝒞 N) :
    SuperCommSMul 𝒞 𝒜 N := by
  intro k i c a hc ha n
  rw [h ha hc n, smul_smul, ← Units.val_mul, ← sgn_add,
    zmod2_superCommSMul_symm, sgn_zero, Units.val_one, one_smul]

section MidBilin

/-- The signed middle action, in closed bilinear form:
`(m, n) ↦ m ⊗ (c•n) - 2 (odd m) ⊗ ((odd c)•n)`. -/
noncomputable def midBilin (c : C) :
    M →ₗ[K] N →ₗ[K] M ⊗[A;K] N :=
  (RelTensor.mk K A M N).compl₁₂ LinearMap.id (Algebra.lsmul K K N c)
    - (2 : ℤ) • ((RelTensor.mk K A M N).compl₁₂ (modProj ℳ 1)
        (Algebra.lsmul K K N (oddPart 𝒞 c)))

omit [Algebra K A] in
theorem midBilin_apply (c : C) (m : M) (n : N) :
    midBilin ℳ 𝒞 c m n
      = RelTensor.mk K A M N m (c • n)
        - (2 : ℤ) • RelTensor.mk K A M N (modProj ℳ 1 m)
            (oddPart 𝒞 c • n) := rfl

omit [Algebra K A] in
/-- **The sign law**: on homogeneous `m ∈ ℳ j`, `c ∈ 𝒞 k` the closed
form is `(-1)^{kj} m ⊗ (c•n)`. -/
theorem midBilin_of_mem {j k : ZMod 2} {m : M} {c : C}
    (hm : m ∈ ℳ j) (hc : c ∈ 𝒞 k) (n : N) :
    midBilin ℳ 𝒞 c m n
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.mk K A M N m (c • n) := by
  rw [midBilin_apply]
  rcases zmod2_cases j with hj | hj <;> rcases zmod2_cases k with hk | hk <;>
      subst hj <;> subst hk
  · rw [modProj_of_mem_ne ℳ hm (by decide), map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem_ne ℳ hm (by decide), map_zero, LinearMap.zero_apply,
      smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_zero 𝒞 hc, zero_smul, map_zero, smul_zero, sub_zero]
    simp
  · rw [modProj_of_mem ℳ hm, oddPart_of_mem_one 𝒞 hc,
      show (1 : ZMod 2) * 1 = 1 from by decide]
    simp only [sgn_one, units_sign_eq, Units.val_neg, Units.val_one,
      neg_smul, one_smul, two_smul]
    abel

omit [Algebra K A] in
theorem midBilin_zero : midBilin (A := A) (N := N) ℳ 𝒞 (0 : C) = 0 := by
  refine LinearMap.ext fun m => LinearMap.ext fun n => ?_
  rw [midBilin_apply]
  simp

omit [Algebra K A] in
theorem midBilin_add (c c' : C) :
    midBilin (A := A) (N := N) ℳ 𝒞 (c + c')
      = midBilin (A := A) (N := N) ℳ 𝒞 c + midBilin (A := A) (N := N) ℳ 𝒞 c' := by
  refine LinearMap.ext fun m => LinearMap.ext fun n => ?_
  rw [LinearMap.add_apply, LinearMap.add_apply, midBilin_apply,
    midBilin_apply, midBilin_apply, add_smul, map_add, map_add, add_smul,
    map_add, smul_add]
  abel

/-- **Balancedness of the signed middle action**: the supercommutation
of the `A`- and `C`-actions makes the closed form balanced. -/
theorem midBalanced [GradedRightSMul 𝒜 ℳ]
    (hsc : SuperCommSMul 𝒜 𝒞 N) (c : C) :
    RelTensor.IsBalanced A (midBilin (A := A) (N := N) ℳ 𝒞 c) := by
  induction c using DirectSum.Decomposition.inductionOn 𝒞 with
  | zero =>
      intro a m n
      rw [midBilin_zero]
      rw [LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply]
  | add c c' hc hc' =>
      intro a m n
      rw [midBilin_add, LinearMap.add_apply, LinearMap.add_apply,
        LinearMap.add_apply, LinearMap.add_apply, hc a m n, hc' a m n]
  | homogeneous xc =>
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
              have sign_id : ∀ k i j : ZMod 2,
                  k * (i + j) + i * k = k * j := by decide
              rw [midBilin_of_mem ℳ 𝒞
                  (GradedRightSMul.smul_mem xa.2 xm.2) xc.2,
                midBilin_of_mem ℳ 𝒞 xm.2 xc.2,
                RelTensor.mk_op_smul, hsc xa.2 xc.2, map_zsmul, smul_smul,
                ← Units.val_mul, ← sgn_add, sign_id]

end MidBilin

/-! ### The descended endomorphism -/

section MidEnd

variable [GradedRightSMul 𝒜 ℳ]

/-- The signed middle action of `c` on `M ⊗[A] N`:
`c • (m ⊗ n) = (-1)^{|c||m|} m ⊗ (c • n)`. -/
noncomputable def midEnd (hsc : SuperCommSMul 𝒜 𝒞 N) (c : C) :
    (M ⊗[A;K] N) →ₗ[K] M ⊗[A;K] N :=
  RelTensor.lift (midBilin ℳ 𝒞 c)
    (midBalanced 𝒜 ℳ 𝒞 hsc c)

theorem midEnd_mk (hsc : SuperCommSMul 𝒜 𝒞 N) (c : C) (m : M) (n : N) :
    midEnd 𝒜 ℳ 𝒞 hsc c (RelTensor.mk K A M N m n)
      = midBilin ℳ 𝒞 c m n := by
  show RelTensor.lift (midBilin ℳ 𝒞 c)
      (midBalanced 𝒜 ℳ 𝒞 hsc c) (RelTensor.mk K A M N m n) = _
  rw [RelTensor.lift_mk]

/-- **The paper's sign convention**, descended: for homogeneous `c`,
`m`, `c • (m ⊗ n) = (-1)^{|c||m|} m ⊗ (c • n)`. -/
theorem midEnd_mk_of_mem (hsc : SuperCommSMul 𝒜 𝒞 N)
    {j k : ZMod 2} {m : M} {c : C} (hm : m ∈ ℳ j) (hc : c ∈ 𝒞 k) (n : N) :
    midEnd 𝒜 ℳ 𝒞 hsc c (RelTensor.mk K A M N m n)
      = ((sgn (k * j) : ℤˣ) : ℤ) • RelTensor.mk K A M N m (c • n) := by
  rw [midEnd_mk, midBilin_of_mem ℳ 𝒞 hm hc]

/-! ### Gradedness -/

variable (𝒩 : ZMod 2 → Submodule K N) [DirectSum.Decomposition 𝒩]

private theorem zmod2_mid_deg :
    ∀ j' k k' : ZMod 2, j' + (k + k') = k + (j' + k') := by
  decide +revert

omit [DirectSum.Decomposition 𝒩] in
/-- The signed middle action is graded. -/
theorem midEnd_mem_relGrading [SetLike.GradedSMul 𝒞 𝒩]
    (hsc : SuperCommSMul 𝒜 𝒞 N) {k j : ZMod 2} {c : C} (hc : c ∈ 𝒞 k)
    {z : M ⊗[A;K] N} (hz : z ∈ relGrading A ℳ 𝒩 j) :
    midEnd 𝒜 ℳ 𝒞 hsc c z ∈ relGrading A ℳ 𝒩 (k + j) := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotGrading_iff (tensorGrading ℳ 𝒩)
    (balancer K A M N)).mp hz
  refine tensorGrading_induction ℳ 𝒩
    (motive := fun w =>
      midEnd 𝒜 ℳ 𝒞 hsc c (RelTensor.fromTensor K A M N w)
        ∈ relGrading A ℳ 𝒩 (k + j)) hx ?_ ?_ ?_ ?_
  · intro j' k' m n hjk hm hn
    show midEnd 𝒜 ℳ 𝒞 hsc c (RelTensor.mk K A M N m n)
        ∈ relGrading A ℳ 𝒩 (k + j)
    rw [midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc hm hc]
    refine zsmul_mem ?_ _
    have h := mk_mem_relGrading (A := A) ℳ 𝒩 hm
      (SetLike.GradedSMul.smul_mem hc hn)
    rwa [vadd_eq_add, zmod2_mid_deg, hjk] at h
  · rw [map_zero, map_zero]
    exact zero_mem _
  · intro x y hx hy
    rw [map_add, map_add]
    exact add_mem hx hy
  · intro c' x hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c' hx

end MidEnd

end Bimod

end Superfusion
