/-
Superfusion / Super / SuperCenterBimod

Milestone M5 (Proposition 2.1), first half: the supercenter of a
super-bimodule and its structure theory.

The supercenter is defined action-theoretically:
  `Ẑ(M) = { m | ∀ b, b • m = ρ(b) m }`
(left action agrees with the signed right action).  Three key facts:

* on the regular bimodule, `Ẑ(A) = superCenter 𝒜` — for a supercentral
  algebra over a field this is `K·1`, of dimension 1;
* the membership condition is expressible in `E`-scalars,
  `(b ᵍ⊗ 1) • m = (1 ᵍ⊗ op b) • m`, hence **every `E`-linear map
  preserves supercenters** — the transfer that reduces Proposition 2.1
  to the regular case;
* the two `E`-structures in play coincide: `superBimoduleAlgHom 𝒜 𝒜 =
  superMulLeftRight 𝒜`, so `wallModule 𝒜 = SuperBimodule.module 𝒜 𝒜`.

Second half (next): uniqueness of the simple `E`-module gives an
`E`-equivalence `A ≃ M` for irreducible `M`, whence `dim Ẑ(M) = 1`;
parity concentration from gradedness of `Ẑ`.
-/
import Superfusion.Super.WallProof

namespace Superfusion

open scoped TensorProduct

section General

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Aᵐᵒᵖ M]
variable [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]

omit [Module A M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] in
theorem signedRSMul_one_left (m : M) : signedRSMul 𝒜 ℳ (1 : A) m = m := by
  rw [signedRSMul_apply, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
    MulOpposite.op_zero, zero_smul, smul_zero, sub_zero, MulOpposite.op_one,
    one_smul]

/-! ### The supercenter of a super-bimodule -/

/-- The supercenter of a super-bimodule: elements on which the left action
agrees with the signed right action, `b • m = (-1)^{|b||m|} m·b`. -/
def superCenterBimod : Submodule K M where
  carrier := {m | ∀ b : A, b • m = signedRSMul 𝒜 ℳ b m}
  zero_mem' := fun b => by rw [smul_zero, map_zero]
  add_mem' := fun {x y} hx hy b => by
    rw [smul_add, map_add, hx b, hy b]
  smul_mem' := fun c x hx b => by
    rw [smul_comm, map_smul, hx b]

omit [SMulCommClass A Aᵐᵒᵖ M] in
theorem mem_superCenterBimod {m : M} :
    m ∈ superCenterBimod 𝒜 ℳ ↔ ∀ b : A, b • m = signedRSMul 𝒜 ℳ b m :=
  Iff.rfl

/-! ### The regular bimodule -/

theorem superCenterBimod_regular :
    superCenterBimod 𝒜 𝒜 = superCenter 𝒜 := by
  apply le_antisymm
  · intro c hc
    apply mem_superCenter_of_comm_signed 𝒜
    intro a
    have h := (mem_superCenterBimod 𝒜 𝒜).mp hc a
    rw [signedRSMul_self_eq_mulMap, smul_eq_mul, SuperOp.mulMap_apply] at h
    exact h
  · have key : ∀ i : ZMod 2, ∀ c ∈ superCenterGrade 𝒜 i,
        c ∈ superCenterBimod 𝒜 𝒜 := by
      intro i c hc
      rw [mem_superCenterBimod]
      intro b
      rw [signedRSMul_self_eq_mulMap, smul_eq_mul]
      induction b using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => rw [zero_mul, map_zero, LinearMap.zero_apply]
      | add u u' hu hu' =>
          rw [add_mul, map_add, LinearMap.add_apply, hu, hu']
      | @homogeneous j m =>
          rw [SuperOp.mulMap_of_mem 𝒜 m.2 hc.1, hc.2 j (m : A) m.2, smul_smul,
            ← Units.val_mul, mul_comm j i, sgn_mul_self', Units.val_one,
            one_smul]
    intro c hc
    rcases Submodule.mem_sup.mp hc with ⟨c₀, hc₀, c₁, hc₁, rfl⟩
    exact (superCenterBimod 𝒜 𝒜).add_mem (key 0 c₀ hc₀) (key 1 c₁ hc₁)

/-! ### The E-scalar characterization and transfer -/

section Transfer

variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

theorem superBimoduleAlgHom_lmul_one (b : A) (m : M) :
    superBimoduleAlgHom 𝒜 ℳ
      ((b ᵍ⊗ₜ[K] (1 : SuperOp 𝒜) : SuperEnvelope 𝒜)) m = b • m := by
  rw [superBimoduleAlgHom_tmul_apply,
    show SuperOp.unop 𝒜 (1 : SuperOp 𝒜) = (1 : A) from rfl,
    signedRSMul_one_left]

theorem superBimoduleAlgHom_one_op (b : A) (m : M) :
    superBimoduleAlgHom 𝒜 ℳ
      (((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 b : SuperEnvelope 𝒜)) m =
      signedRSMul 𝒜 ℳ b m := by
  rw [superBimoduleAlgHom_tmul_apply, SuperOp.unop_op, one_smul]

/-- The supercenter condition, written in `E`-scalars. -/
theorem mem_superCenterBimod_iff_E {m : M} :
    m ∈ superCenterBimod 𝒜 ℳ ↔
      ∀ b : A,
        superBimoduleAlgHom 𝒜 ℳ
          ((b ᵍ⊗ₜ[K] (1 : SuperOp 𝒜) : SuperEnvelope 𝒜)) m =
        superBimoduleAlgHom 𝒜 ℳ
          (((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 b : SuperEnvelope 𝒜)) m := by
  simp only [superBimoduleAlgHom_lmul_one, superBimoduleAlgHom_one_op]
  exact Iff.rfl

/-- **`E`-equivariant maps preserve supercenters** — the transfer lemma
behind Proposition 2.1 (stated instance-free, via the assembled algebra
actions). -/
theorem map_superCenterBimod (φ : A →ₗ[K] M)
    (hφ : ∀ (e : SuperEnvelope 𝒜) (x : A),
      φ (superBimoduleAlgHom 𝒜 𝒜 e x) = superBimoduleAlgHom 𝒜 ℳ e (φ x))
    {x : A} (hx : x ∈ superCenterBimod 𝒜 𝒜) :
    φ x ∈ superCenterBimod 𝒜 ℳ := by
  rw [mem_superCenterBimod_iff_E] at hx ⊢
  intro b
  rw [← hφ, ← hφ, hx b]

end Transfer

/-! ### The two E-structures coincide -/

/-- On the regular bimodule the assembled action is the Wall map. -/
theorem superBimoduleAlgHom_self :
    superBimoduleAlgHom 𝒜 𝒜 = superMulLeftRight 𝒜 := by
  apply AlgHom.toLinearMap_injective
  apply GradedTensorProduct.hom_ext
  apply TensorProduct.ext'
  intro a b
  refine LinearMap.ext fun x => ?_
  show superBimoduleAlgHom 𝒜 𝒜 (a ᵍ⊗ₜ[K] b) x =
    superMulLeftRight 𝒜 (a ᵍ⊗ₜ[K] b) x
  rw [superBimoduleAlgHom_tmul_apply, superMulLeftRight_tmul_apply,
    signedRSMul_self_eq_mulMap, smul_eq_mul]

/-- The Wall module structure is the regular super-bimodule structure. -/
theorem wallModule_eq_superBimodule :
    wallModule 𝒜 = SuperBimodule.module 𝒜 𝒜 := by
  show Module.compHom A (superMulLeftRight 𝒜).toRingHom =
    Module.compHom A (superBimoduleAlgHom 𝒜 𝒜).toRingHom
  rw [superBimoduleAlgHom_self]

end General

/-! ### Dimension of the regular supercenter -/

section Rank

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

theorem finrank_superCenterBimod_regular [IsSuperCentral 𝒜] [Nontrivial A] :
    Module.finrank K (superCenterBimod 𝒜 𝒜) = 1 := by
  rw [superCenterBimod_regular, superCenter_eq_one 𝒜, Submodule.one_eq_span]
  exact finrank_span_singleton one_ne_zero

end Rank

end Superfusion
