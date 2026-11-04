/-
Superfusion / Bimod / Basic

Milestone M8a-1: **super `(A,B)`-bimodules** — the element-level bimodule
track.  The paper's §4.1 works with bimodules over *two different*
superalgebras: the column bimodule `C_{a,b}` is a
`(D_a ⊗̂ D_b, D_{a+b})`-bimodule, and the iterated fusions `B_L`, `B_R`
are `(D_a ⊗̂ D_b ⊗̂ D_c, D_{abc})`-bimodules.

Design (inherited from the `(A,A)` layer of M3, `Super/Bimodule.lean`):
the bimodule AXIOMS are sign-free —
  `[Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]`
plus a grading `ℳ : ZMod 2 → Submodule K M` with both actions graded
(`SetLike.GradedSMul 𝒜 ℳ` on the left, `GradedRightSMul ℬ ℳ` on the
right).  The Koszul sign enters only through the **signed right action**
`ρ(b) m = (-1)^{|b||m|} (m · b)` (`signedRSMul ℬ ℳ`, reused verbatim from
M3, which is already algebra-general), which is multiplicative over the
super-opposite `B^sop` and supercommutes with the left `A`-action; via
mathlib's `GradedTensorProduct.lift` the two actions assemble into an
algebra map
  `actionHom : E_{A,B} = A ⊗̂ B^sop →ₐ[K] End_K M`,
i.e. a `Module E_{A,B} M` (`Bimod.module`, a `def` to be activated as a
local instance, mirroring `TensorProduct.Algebra.module`).  On homogeneous
elements the action is the paper's
  `(a ⊗ b) · m = (-1)^{|b||m|} a m b`.

Only the algebra-map layer is new here: the `(A,A)` file's
`signedRSMulAlgHom`/`superBimoduleAlgHom` carry a spurious left
`A`-action hypothesis by section-variable inclusion, so they cannot be
instantiated at two different algebras.  At `B = A` our envelope action
is *definitionally* the M3 one (`actionHom_self`), so the regular-bimodule
theory (Prop 2.1, super Skolem–Noether) applies unchanged.

Sign conventions: (C4)–(C5) and the ᵍ⊗-conventions of Appendix A, routed
through `sgn` as everywhere in this project.
-/
import Superfusion.Super.Bimodule

namespace Superfusion

namespace Bimod

open scoped TensorProduct

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]

/-! ### The right action as an algebra map on the super-opposite

`signedRSMul ℬ ℳ`, `signedRSMul_of_mem`, and `GradedRightSMul ℬ ℳ` are
already fully general in M3; only the algebra-map packaging has to be
redone without the `(A,A)` section baggage. -/

section RightAction

variable [Module Bᵐᵒᵖ M] [IsScalarTower K Bᵐᵒᵖ M] [GradedRightSMul ℬ ℳ]

/-- The signed right action of `B` on a graded right module, as an algebra
map `B^sop →ₐ End_K M` — the Koszul sign is what makes it multiplicative
over the super-opposite.  (The general-`B` version of M3's
`signedRSMulAlgHom`.) -/
noncomputable def rightActionHom : SuperOp ℬ →ₐ[K] Module.End K M where
  toFun b := signedRSMul ℬ ℳ (SuperOp.unop ℬ b)
  map_one' := LinearMap.ext fun m => by
    show signedRSMul ℬ ℳ (1 : B) m = m
    rw [signedRSMul_apply, oddPart_of_mem_zero ℬ (SetLike.one_mem_graded ℬ),
      MulOpposite.op_zero, zero_smul, smul_zero, sub_zero, MulOpposite.op_one,
      one_smul]
  map_mul' b b' := by
    have sign_id : ∀ j j' i : ZMod 2,
        j * j' + (j' + j) * i = j' * i + j * (j' + i) := by decide
    refine LinearMap.ext fun m => ?_
    show signedRSMul ℬ ℳ
        (SuperOp.mulMap ℬ (SuperOp.unop ℬ b) (SuperOp.unop ℬ b')) m
      = signedRSMul ℬ ℳ (SuperOp.unop ℬ b)
          (signedRSMul ℬ ℳ (SuperOp.unop ℬ b') m)
    induction SuperOp.unop ℬ b using DirectSum.Decomposition.inductionOn ℬ with
    | zero =>
        simp only [map_zero, LinearMap.zero_apply]
    | add u u' hu hu' =>
        simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
        rw [hu, hu']
    | homogeneous mu =>
      induction SuperOp.unop ℬ b' using DirectSum.Decomposition.inductionOn ℬ with
      | zero =>
          simp only [map_zero, LinearMap.zero_apply]
      | add u u' hu hu' =>
          simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
          rw [hu, hu']
      | homogeneous mu' =>
        induction m using DirectSum.Decomposition.inductionOn ℳ with
        | zero => simp only [map_zero]
        | add m m' hm hm' =>
            simp only [map_add] at hm hm' ⊢
            rw [hm, hm']
        | homogeneous mm =>
            rw [SuperOp.mulMap_of_mem ℬ mu.2 mu'.2, map_zsmul,
              LinearMap.smul_apply,
              signedRSMul_of_mem ℬ ℳ (SetLike.mul_mem_graded mu'.2 mu.2) mm.2,
              signedRSMul_of_mem ℬ ℳ mu'.2 mm.2, map_zsmul,
              signedRSMul_of_mem ℬ ℳ mu.2 (GradedRightSMul.smul_mem mu'.2 mm.2),
              smul_smul, smul_smul, ← mul_smul, ← MulOpposite.op_mul,
              ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add,
              sign_id]
  map_zero' := by
    show signedRSMul ℬ ℳ (SuperOp.unop ℬ 0) = 0
    rw [map_zero, map_zero]
  map_add' b b' := by
    show signedRSMul ℬ ℳ (SuperOp.unop ℬ (b + b')) = _
    rw [map_add, map_add]
  commutes' r := LinearMap.ext fun m => by
    show signedRSMul ℬ ℳ (algebraMap K B r) m = algebraMap K (Module.End K M) r m
    rw [signedRSMul_apply,
      oddPart_of_mem_zero ℬ (algebraMap_mem_grade_zero ℬ r),
      MulOpposite.op_zero, zero_smul, smul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, smul_assoc,
      MulOpposite.op_one, one_smul, Module.algebraMap_end_apply]

theorem rightActionHom_apply (b : SuperOp ℬ) (m : M) :
    rightActionHom ℬ ℳ b m = signedRSMul ℬ ℳ (SuperOp.unop ℬ b) m := rfl

end RightAction

/-! ### The enveloping superalgebra of a pair -/

/-- The enveloping superalgebra `E_{A,B} = A ⊗̂ B^sop` of a pair of
superalgebras (Koszul-signed tensor product, from mathlib); super
`(A,B)`-bimodules are its modules.  At `B = A` this is `SuperEnvelope 𝒜`. -/
noncomputable abbrev Envelope :=
  𝒜 ᵍ⊗[K] (SuperOp.grading ℬ)

section Envelope

variable [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
variable [IsScalarTower K A M] [IsScalarTower K Bᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul ℬ ℳ]

omit [GradedAlgebra 𝒜] in
/-- Left `A`-action and signed right `B`-action supercommute — the
hypothesis of `GradedTensorProduct.lift`.  (Sign-free axiom
`SMulCommClass A Bᵐᵒᵖ M` in, Koszul-signed statement out.) -/
theorem lsmul_rightActionHom_anticommutes ⦃i j : ZMod 2⦄
    (a : 𝒜 i) (b : SuperOp.grading ℬ j) :
    Algebra.lsmul K K M (a : A) * rightActionHom ℬ ℳ b =
      (-1 : ℤˣ) ^ (j * i) •
        (rightActionHom ℬ ℳ b * Algebra.lsmul K K M (a : A)) := by
  have hb : SuperOp.unop ℬ (b : SuperOp ℬ) ∈ ℬ j := b.2
  have sign_id : ∀ j i k : ZMod 2, j * i + j * (i + k) = j * k := by decide
  refine LinearMap.ext fun m => ?_
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp only [map_zero]
  | add m m' hm hm' =>
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_add] at hm hm' ⊢
      rw [hm, hm']
  | homogeneous mm =>
      rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
        rightActionHom_apply, rightActionHom_apply,
        signedRSMul_of_mem ℬ ℳ hb mm.2, map_zsmul]
      simp only [show ∀ m' : M, Algebra.lsmul K K M (a : A) m' = (a : A) • m'
        from fun _ => rfl]
      rw [signedRSMul_of_mem ℬ ℳ hb (SetLike.GradedSMul.smul_mem a.2 mm.2),
        Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul, ← Units.val_mul,
        ← sgn_add, vadd_eq_add, sign_id, smul_comm (a : A)]

/-- The two actions of a super `(A,B)`-bimodule assemble into an algebra
map `E_{A,B} →ₐ[K] End_K M`. -/
noncomputable def actionHom : Envelope 𝒜 ℬ →ₐ[K] Module.End K M :=
  GradedTensorProduct.lift 𝒜 (SuperOp.grading ℬ)
    (Algebra.lsmul K K M) (rightActionHom ℬ ℳ)
    (lsmul_rightActionHom_anticommutes 𝒜 ℬ ℳ)

theorem actionHom_tmul_apply (a : A) (b : SuperOp ℬ) (m : M) :
    actionHom 𝒜 ℬ ℳ (a ᵍ⊗ₜ[K] b) m =
      a • signedRSMul ℬ ℳ (SuperOp.unop ℬ b) m := by
  rw [actionHom, GradedTensorProduct.lift_tmul]
  rfl

/-- On homogeneous elements the envelope action is the paper's
`(a ⊗ b) · m = (-1)^{|b||m|} a m b`. -/
theorem actionHom_tmul_apply_of_mem {j k : ZMod 2} (a : A) {b : SuperOp ℬ}
    (hb : SuperOp.unop ℬ b ∈ ℬ j) {m : M} (hm : m ∈ ℳ k) :
    actionHom 𝒜 ℬ ℳ (a ᵍ⊗ₜ[K] b) m =
      ((sgn (j * k) : ℤˣ) : ℤ) •
        (a • (MulOpposite.op (SuperOp.unop ℬ b) • m)) := by
  rw [actionHom_tmul_apply, signedRSMul_of_mem ℬ ℳ hb hm, smul_comm]

/-- The envelope action is graded: homogeneous elements of `E_{A,B}` shift
the module grading by their total degree. -/
theorem actionHom_tmul_smul_mem {i j k : ZMod 2} {a : A} (ha : a ∈ 𝒜 i)
    {b : SuperOp ℬ} (hb : SuperOp.unop ℬ b ∈ ℬ j) {m : M} (hm : m ∈ ℳ k) :
    actionHom 𝒜 ℬ ℳ (a ᵍ⊗ₜ[K] b) m ∈ ℳ (i + (j + k)) := by
  rw [actionHom_tmul_apply, signedRSMul_of_mem ℬ ℳ hb hm]
  exact SetLike.GradedSMul.smul_mem ha
    (zsmul_mem (GradedRightSMul.smul_mem hb hm) _)

/-- **A super `(A,B)`-bimodule is an `E_{A,B}`-module** (the Koszul sign
lives in the action, not in the axioms).  A `def` to be activated as a
local instance, mirroring `TensorProduct.Algebra.module`. -/
noncomputable abbrev module : Module (Envelope 𝒜 ℬ) M :=
  Module.compHom M (actionHom 𝒜 ℬ ℳ).toRingHom

end Envelope

/-! ### Compatibility with the `(A,A)` layer -/

section Compat

variable [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
variable [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

/-- At `B = A` the pair envelope action is definitionally the `(A,A)`
action of M3 — the regular-bimodule theory (Prop 2.1, super
Skolem–Noether) applies to the pair framework unchanged. -/
theorem actionHom_self : actionHom 𝒜 𝒜 ℳ = superBimoduleAlgHom 𝒜 ℳ := rfl

end Compat

end Bimod

end Superfusion
