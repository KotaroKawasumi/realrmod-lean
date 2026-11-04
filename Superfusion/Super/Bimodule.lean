/-
Superfusion / Super / Bimodule

Milestone M3: super (A,A)-bimodules and their module structure over the
enveloping superalgebra `E = A ⊗̂ A^sop`.

Design (docs/super-track-design.md): the bimodule AXIOMS are sign-free —
`[Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]` plus a grading
`ℳ : ZMod 2 → Submodule K M` with both actions graded.  The Koszul sign
enters only through the **signed right action**
  `ρ(b) m = (-1)^{|b||m|} (m · b)`,
which (same trick as M1/M2) has the closed bilinear form
  `ρ(b) m = op b • m - 2 · (op (oddPart b) • oddPartMod m)`.
Together with the left action it assembles, via mathlib's
`GradedTensorProduct.lift`, into an algebra map `E →ₐ End_K M`, i.e. an
`E`-module structure on `M` (`SuperBimodule.module`, a `def` to be
activated as a local instance, mirroring `TensorProduct.Algebra.module`).

The regular bimodule `M = A` recovers the multiplication map of the
super-opposite, hence the Wall map of M2
(`signedRSMul_self_eq_mulMap`).
-/
import Superfusion.Super.Wall
import Mathlib.Algebra.GradedMulAction

namespace Superfusion

open scoped TensorProduct

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]

/-! ### The odd projection of a graded module -/

/-- The odd projection of a `ZMod 2`-decomposed module. -/
noncomputable def oddPartMod : M →ₗ[K] M :=
  (ℳ 1).subtype ∘ₗ
    DirectSum.component K (ZMod 2) (fun i => ↥(ℳ i)) 1 ∘ₗ
      (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem oddPartMod_of_mem_one {m : M} (hm : m ∈ ℳ 1) : oddPartMod ℳ m = m := by
  show (DirectSum.decompose ℳ m 1 : M) = m
  rw [DirectSum.decompose_of_mem_same ℳ hm]

theorem oddPartMod_of_mem_zero {m : M} (hm : m ∈ ℳ 0) : oddPartMod ℳ m = 0 := by
  show (DirectSum.decompose ℳ m 1 : M) = 0
  rw [DirectSum.decompose_of_mem_ne ℳ hm (by decide)]

/-- On the algebra itself, the module-level odd projection is the algebra
one. -/
theorem oddPartMod_eq_oddPart : oddPartMod 𝒜 = oddPart 𝒜 := rfl

/-! ### Graded actions -/

/-- The right action of a superalgebra on a graded module is graded.
(The left-action counterpart is mathlib's `SetLike.GradedSMul 𝒜 ℳ`.) -/
class GradedRightSMul [Module Aᵐᵒᵖ M] : Prop where
  smul_mem : ∀ ⦃i j : ZMod 2⦄ ⦃a : A⦄ ⦃m : M⦄,
    a ∈ 𝒜 i → m ∈ ℳ j → MulOpposite.op a • m ∈ ℳ (i + j)

section RightAction

variable [Module Aᵐᵒᵖ M] [IsScalarTower K Aᵐᵒᵖ M]

/-- The (unsigned) right action, bundled as a `K`-bilinear map. -/
noncomputable def rsmulBilin : A →ₗ[K] M →ₗ[K] M :=
  LinearMap.mk₂ K (fun a m => MulOpposite.op a • m)
    (fun a a' m => by rw [MulOpposite.op_add, add_smul])
    (fun c a m => by rw [MulOpposite.op_smul, smul_assoc])
    (fun a m m' => smul_add _ _ _)
    (fun c a m => smul_comm _ _ _)

@[simp] theorem rsmulBilin_apply (a : A) (m : M) :
    rsmulBilin (K := K) a m = MulOpposite.op a • m := rfl

/-- The **signed right action** `ρ(b) m = (-1)^{|b||m|} (m · b)`, in closed
bilinear form. -/
noncomputable def signedRSMul : A →ₗ[K] M →ₗ[K] M :=
  rsmulBilin - (2 : ℤ) • (rsmulBilin.compl₁₂ (oddPart 𝒜) (oddPartMod ℳ))

theorem signedRSMul_apply (b : A) (m : M) :
    signedRSMul 𝒜 ℳ b m =
      MulOpposite.op b • m -
        (2 : ℤ) • (MulOpposite.op (oddPart 𝒜 b) • oddPartMod ℳ m) := rfl

/-- The sign law: for `b ∈ 𝒜 j` and `m ∈ ℳ i`,
`ρ(b) m = (-1)^{ji} (op b • m)`. -/
theorem signedRSMul_of_mem {j i : ZMod 2} {b : A} {m : M}
    (hb : b ∈ 𝒜 j) (hm : m ∈ ℳ i) :
    signedRSMul 𝒜 ℳ b m =
      ((sgn (j * i) : ℤˣ) : ℤ) • (MulOpposite.op b • m) := by
  rw [signedRSMul_apply]
  rcases zmod2_cases j with hj | hj <;> rcases zmod2_cases i with hi | hi <;>
      subst hj <;> subst hi
  · rw [oddPartMod_of_mem_zero ℳ hm, smul_zero, smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_zero 𝒜 hb, MulOpposite.op_zero, zero_smul, smul_zero,
      sub_zero]
    simp
  · rw [oddPartMod_of_mem_zero ℳ hm, smul_zero, smul_zero, sub_zero]
    simp
  · rw [oddPart_of_mem_one 𝒜 hb, oddPartMod_of_mem_one ℳ hm,
      show (1 : ZMod 2) * 1 = 1 from by decide]
    simp only [sgn_one, units_sign_eq, Units.val_neg, Units.val_one, neg_smul,
      one_smul, two_smul]
    abel

end RightAction

/-! ### The E-module structure -/

section Envelope

variable [Module A M] [Module Aᵐᵒᵖ M]
variable [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

/-- The signed right action as an algebra map `A^sop →ₐ End_K M` — the
Koszul sign is what makes it multiplicative over the super-opposite. -/
noncomputable def signedRSMulAlgHom : SuperOp 𝒜 →ₐ[K] Module.End K M where
  toFun b := signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 b)
  map_one' := LinearMap.ext fun m => by
    show signedRSMul 𝒜 ℳ (1 : A) m = m
    rw [signedRSMul_apply, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
      MulOpposite.op_zero, zero_smul, smul_zero, sub_zero, MulOpposite.op_one,
      one_smul]
  map_mul' b b' := by
    have sign_id : ∀ j j' i : ZMod 2,
        j * j' + (j' + j) * i = j' * i + j * (j' + i) := by decide
    refine LinearMap.ext fun m => ?_
    show signedRSMul 𝒜 ℳ
        (SuperOp.mulMap 𝒜 (SuperOp.unop 𝒜 b) (SuperOp.unop 𝒜 b')) m
      = signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 b)
          (signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 b') m)
    induction SuperOp.unop 𝒜 b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero =>
        simp only [map_zero, LinearMap.zero_apply]
    | add u u' hu hu' =>
        simp only [map_add, LinearMap.add_apply] at hu hu' ⊢
        rw [hu, hu']
    | homogeneous mu =>
      induction SuperOp.unop 𝒜 b' using DirectSum.Decomposition.inductionOn 𝒜 with
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
            rw [SuperOp.mulMap_of_mem 𝒜 mu.2 mu'.2, map_zsmul,
              LinearMap.smul_apply,
              signedRSMul_of_mem 𝒜 ℳ (SetLike.mul_mem_graded mu'.2 mu.2) mm.2,
              signedRSMul_of_mem 𝒜 ℳ mu'.2 mm.2, map_zsmul,
              signedRSMul_of_mem 𝒜 ℳ mu.2 (GradedRightSMul.smul_mem mu'.2 mm.2),
              smul_smul, smul_smul, ← mul_smul, ← MulOpposite.op_mul,
              ← Units.val_mul, ← Units.val_mul, ← sgn_add, ← sgn_add,
              sign_id]
  map_zero' := by
    show signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 0) = 0
    rw [map_zero, map_zero]
  map_add' b b' := by
    show signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 (b + b')) = _
    rw [map_add, map_add]
  commutes' r := LinearMap.ext fun m => by
    show signedRSMul 𝒜 ℳ (algebraMap K A r) m = algebraMap K (Module.End K M) r m
    rw [signedRSMul_apply,
      oddPart_of_mem_zero 𝒜 (algebraMap_mem_grade_zero 𝒜 r),
      MulOpposite.op_zero, zero_smul, smul_zero, sub_zero,
      Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, smul_assoc,
      MulOpposite.op_one, one_smul, Module.algebraMap_end_apply]

omit [Module A M] [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M]
  [SetLike.GradedSMul 𝒜 ℳ] in
theorem signedRSMulAlgHom_apply (b : SuperOp 𝒜) (m : M) :
    signedRSMulAlgHom 𝒜 ℳ b m = signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 b) m := rfl

/-- Left action and signed right action supercommute — the hypothesis of
`GradedTensorProduct.lift`. -/
theorem lsmul_signedRSMul_anticommutes ⦃i j : ZMod 2⦄
    (a : 𝒜 i) (b : SuperOp.grading 𝒜 j) :
    Algebra.lsmul K K M (a : A) * signedRSMulAlgHom 𝒜 ℳ b =
      (-1 : ℤˣ) ^ (j * i) •
        (signedRSMulAlgHom 𝒜 ℳ b * Algebra.lsmul K K M (a : A)) := by
  have hb : SuperOp.unop 𝒜 (b : SuperOp 𝒜) ∈ 𝒜 j := b.2
  have sign_id : ∀ j i k : ZMod 2, j * i + j * (i + k) = j * k := by decide
  refine LinearMap.ext fun m => ?_
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp only [map_zero]
  | add m m' hm hm' =>
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_add] at hm hm' ⊢
      rw [hm, hm']
  | homogeneous mm =>
      rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply,
        signedRSMulAlgHom_apply, signedRSMulAlgHom_apply,
        signedRSMul_of_mem 𝒜 ℳ hb mm.2, map_zsmul]
      simp only [show ∀ m' : M, Algebra.lsmul K K M (a : A) m' = (a : A) • m'
        from fun _ => rfl]
      rw [signedRSMul_of_mem 𝒜 ℳ hb (SetLike.GradedSMul.smul_mem a.2 mm.2),
        Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul, ← Units.val_mul,
        ← sgn_add, vadd_eq_add, sign_id, smul_comm (a : A)]

/-- The two actions of a super-bimodule assemble into an algebra map
`E →ₐ[K] End_K M` on the enveloping superalgebra. -/
noncomputable def superBimoduleAlgHom : SuperEnvelope 𝒜 →ₐ[K] Module.End K M :=
  GradedTensorProduct.lift 𝒜 (SuperOp.grading 𝒜)
    (Algebra.lsmul K K M) (signedRSMulAlgHom 𝒜 ℳ)
    (lsmul_signedRSMul_anticommutes 𝒜 ℳ)

theorem superBimoduleAlgHom_tmul_apply (a : A) (b : SuperOp 𝒜) (m : M) :
    superBimoduleAlgHom 𝒜 ℳ (a ᵍ⊗ₜ[K] b) m =
      a • signedRSMul 𝒜 ℳ (SuperOp.unop 𝒜 b) m := by
  rw [superBimoduleAlgHom, GradedTensorProduct.lift_tmul]
  rfl

/-- **A super-bimodule is an `E`-module** (the Koszul sign lives in the
action, not in the axioms).  A `def` to be activated as a local instance,
mirroring `TensorProduct.Algebra.module`. -/
noncomputable abbrev SuperBimodule.module : Module (SuperEnvelope 𝒜) M :=
  Module.compHom M (superBimoduleAlgHom 𝒜 ℳ).toRingHom

end Envelope

/-! ### The regular bimodule -/

section Regular

/-- The right action of a superalgebra on itself is graded. -/
instance : GradedRightSMul 𝒜 𝒜 where
  smul_mem {i j} a x ha hx := by
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    exact add_comm j i ▸ SetLike.mul_mem_graded hx ha

/-- On the regular bimodule the signed right action is the multiplication
map of the super-opposite — the very map whose lift is the Wall map of M2. -/
theorem signedRSMul_self_eq_mulMap :
    signedRSMul 𝒜 𝒜 = SuperOp.mulMap 𝒜 := by
  refine LinearMap.ext fun a => LinearMap.ext fun x => ?_
  rw [signedRSMul_apply, SuperOp.mulMap_apply, oddPartMod_eq_oddPart,
    MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, MulOpposite.unop_op]

end Regular

end Superfusion
