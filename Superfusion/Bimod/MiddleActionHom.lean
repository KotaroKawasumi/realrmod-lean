/-
Superfusion / Bimod / MiddleActionHom

Milestone M8a-7b: **the `(ℬ ᵍ⊗ 𝒞)`-module structure of `M ⊗[A] N`**.
The signed middle action of M8a-7a is multiplicative over `C` (the
Koszul sign consumes only the parity of `m`, so no super-opposite is
needed): `midAlgHom : C →ₐ[K] End_K (M ⊗[A] N)`.  It supercommutes
with the outer left action (`leftActionEnd_anticommutes_midAlgHom`),
so the two assemble via `GradedTensorProduct.lift` into

  `gtensorLeftActionHom : ℬ ᵍ⊗[K] 𝒞 →ₐ[K] End_K (M ⊗[A] N)`,

acting on homogeneous elements by the handoff convention

  `(b ᵍ⊗ c) • (u ⊗ v) = (-1)^{|c||u|} (b•u) ⊗ (c•v)`

(`gtensorLeftActionHom_tmul_mk_of_mem`) — for `B_L` this is the left
`(D_a ⊗̂ D_b) ⊗̂ D_c`-action of §4.1.  The middle action also strictly
commutes with the outer right action (`midEnd_comm_rightActionEnd`),
completing the super-bimodule picture.
-/
import Superfusion.Bimod.MiddleAction

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
variable [GradedRightSMul 𝒜 ℳ]

/-! ### The middle action as an algebra map -/

theorem midEnd_zero (hsc : SuperCommSMul 𝒜 𝒞 N) :
    midEnd 𝒜 ℳ 𝒞 hsc (0 : C) = 0 :=
  RelTensor.hom_ext fun m n => by
    rw [midEnd_mk, midBilin_zero, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply]

theorem midEnd_add (hsc : SuperCommSMul 𝒜 𝒞 N) (c c' : C) :
    midEnd 𝒜 ℳ 𝒞 hsc (c + c')
      = midEnd 𝒜 ℳ 𝒞 hsc c + midEnd 𝒜 ℳ 𝒞 hsc c' :=
  RelTensor.hom_ext fun m n => by
    rw [midEnd_mk, midBilin_add, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.add_apply, midEnd_mk, midEnd_mk]

/-- The signed middle action is an algebra map `C →ₐ End_K (M ⊗[A] N)`
(the Koszul sign consumes only the parity of the `M`-slot, so it is
plainly multiplicative). -/
noncomputable def midAlgHom (hsc : SuperCommSMul 𝒜 𝒞 N) :
    C →ₐ[K] Module.End K (M ⊗[A;K] N) where
  toFun := midEnd 𝒜 ℳ 𝒞 hsc
  map_one' := RelTensor.hom_ext fun m n => by
    rw [Module.End.one_apply, midEnd_mk, midBilin_apply,
      oddPart_of_mem_zero 𝒞 (SetLike.one_mem_graded 𝒞), zero_smul,
      map_zero, smul_zero, sub_zero, one_smul]
  map_mul' c c' := RelTensor.hom_ext fun m n => by
    rw [Module.End.mul_apply]
    induction m using DirectSum.Decomposition.inductionOn ℳ with
    | zero =>
        have h0 : RelTensor.mk K A M N (0 : M) n = 0 := by
          rw [map_zero, LinearMap.zero_apply]
        rw [h0, map_zero, map_zero, map_zero]
    | add m m' hm hm' =>
        rw [LinearMap.map_add₂, map_add, map_add, map_add, hm, hm']
    | homogeneous xm =>
        induction c using DirectSum.Decomposition.inductionOn 𝒞 with
        | zero =>
            rw [zero_mul, midEnd_zero 𝒜 ℳ 𝒞 hsc, LinearMap.zero_apply,
              LinearMap.zero_apply]
        | add c₁ c₂ h₁ h₂ =>
            rw [add_mul, midEnd_add 𝒜 ℳ 𝒞 hsc, midEnd_add 𝒜 ℳ 𝒞 hsc c₁ c₂,
              LinearMap.add_apply, LinearMap.add_apply, h₁, h₂]
        | homogeneous xc =>
            induction c' using DirectSum.Decomposition.inductionOn 𝒞 with
            | zero =>
                rw [mul_zero, midEnd_zero 𝒜 ℳ 𝒞 hsc, LinearMap.zero_apply,
                  map_zero]
            | add c₁ c₂ h₁ h₂ =>
                rw [mul_add, midEnd_add 𝒜 ℳ 𝒞 hsc, midEnd_add 𝒜 ℳ 𝒞 hsc c₁ c₂,
                  LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]
            | homogeneous xc' =>
                have sign_id : ∀ k k' j : ZMod 2,
                    k' * j + k * j = (k + k') * j := by decide
                rw [midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2
                    (SetLike.mul_mem_graded xc.2 xc'.2),
                  midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2 xc'.2, map_zsmul,
                  midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2 xc.2,
                  smul_smul, ← Units.val_mul, ← sgn_add, sign_id, mul_smul]
  map_zero' := midEnd_zero 𝒜 ℳ 𝒞 hsc
  map_add' := midEnd_add 𝒜 ℳ 𝒞 hsc
  commutes' r := RelTensor.hom_ext fun m n => by
    rw [Module.algebraMap_end_apply, midEnd_mk, midBilin_apply,
      oddPart_of_mem_zero 𝒞 (algebraMap_mem_grade_zero 𝒞 r), zero_smul,
      map_zero, smul_zero, sub_zero, algebraMap_smul, map_smul]

theorem midAlgHom_apply (hsc : SuperCommSMul 𝒜 𝒞 N) (c : C) :
    midAlgHom 𝒜 ℳ 𝒞 hsc c = midEnd 𝒜 ℳ 𝒞 hsc c := rfl

/-! ### Supercommutation with the outer left action -/

section Left

variable {B : Type*} [Ring B] [Algebra K B]
variable [Module B M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower K B M]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable [SetLike.GradedSMul ℬ ℳ]

omit [GradedAlgebra ℬ] in
/-- The outer left action and the signed middle action supercommute —
the hypothesis of `GradedTensorProduct.lift`. -/
theorem leftActionEnd_anticommutes_midAlgHom
    (hsc : SuperCommSMul 𝒜 𝒞 N) ⦃i k : ZMod 2⦄ (b : ℬ i) (c : 𝒞 k) :
    leftActionEnd K A M N (b : B) * midAlgHom 𝒜 ℳ 𝒞 hsc (c : C)
      = (-1 : ℤˣ) ^ (k * i) •
          (midAlgHom 𝒜 ℳ 𝒞 hsc (c : C) * leftActionEnd K A M N (b : B)) := by
  have sign_id : ∀ k i j : ZMod 2, k * i + k * (i + j) = k * j := by decide
  refine RelTensor.hom_ext fun m n => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply]
  induction m using DirectSum.Decomposition.inductionOn ℳ with
  | zero =>
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | add m m' hm hm' =>
      simp only [map_add, LinearMap.add_apply, hm, hm', smul_add]
  | homogeneous xm =>
      rw [midAlgHom_apply, midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc xm.2 c.2, map_zsmul,
        leftActionEnd_mk, leftActionEnd_mk,
        midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc
          ((vadd_eq_add (i : ZMod 2) _) ▸ SetLike.GradedSMul.smul_mem b.2 xm.2)
          c.2,
        Units.smul_def, ← sgn_eq_neg_one_uzpow, smul_smul, ← Units.val_mul,
        ← sgn_add, sign_id]

/-- **The `(ℬ ᵍ⊗ 𝒞)`-module structure**: the outer left action and the
signed middle action assemble on the graded tensor product. -/
noncomputable def gtensorLeftActionHom (hsc : SuperCommSMul 𝒜 𝒞 N) :
    (ℬ ᵍ⊗[K] 𝒞) →ₐ[K] Module.End K (M ⊗[A;K] N) :=
  GradedTensorProduct.lift ℬ 𝒞
    (leftActionEnd K A M N) (midAlgHom 𝒜 ℳ 𝒞 hsc)
    (leftActionEnd_anticommutes_midAlgHom 𝒜 ℳ 𝒞 ℬ hsc)

/-- **The handoff convention** (§4.1): on homogeneous elements
`(b ᵍ⊗ c) • (u ⊗ v) = (-1)^{|c||u|} (b•u) ⊗ (c•v)`. -/
theorem gtensorLeftActionHom_tmul_mk_of_mem (hsc : SuperCommSMul 𝒜 𝒞 N)
    {j k : ZMod 2} (b : B) {c : C} (hc : c ∈ 𝒞 k)
    {u : M} (hu : u ∈ ℳ j) (v : N) :
    gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc (b ᵍ⊗ₜ[K] c)
        (RelTensor.mk K A M N u v)
      = ((sgn (k * j) : ℤˣ) : ℤ) •
          RelTensor.mk K A M N (b • u) (c • v) := by
  rw [gtensorLeftActionHom, GradedTensorProduct.lift_tmul]
  rw [Module.End.mul_apply, midAlgHom_apply,
    midEnd_mk_of_mem 𝒜 ℳ 𝒞 hsc hu hc, map_zsmul, leftActionEnd_mk]

/-- At the left slot embedding, `gtensorLeftActionHom` is exactly the
outer left action.  No homogeneity assumption is needed. -/
theorem gtensorLeftActionHom_includeLeft
    (hsc : SuperCommSMul 𝒜 𝒞 N) (b : B) :
    gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc
        (GradedTensorProduct.includeLeft ℬ 𝒞 b) =
      leftActionEnd K A M N b := by
  show gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc
      (b ᵍ⊗ₜ[K] (1 : C)) = _
  rw [gtensorLeftActionHom, GradedTensorProduct.lift_tmul,
    map_one, mul_one]

/-- At the right slot embedding, `gtensorLeftActionHom` is exactly the
signed middle action.  No homogeneity assumption is needed. -/
theorem gtensorLeftActionHom_includeRight
    (hsc : SuperCommSMul 𝒜 𝒞 N) (c : C) :
    gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc
        (GradedTensorProduct.includeRight ℬ 𝒞 c) =
      midAlgHom 𝒜 ℳ 𝒞 hsc c := by
  show gtensorLeftActionHom 𝒜 ℳ 𝒞 ℬ hsc
      ((1 : B) ᵍ⊗ₜ[K] c) = _
  rw [gtensorLeftActionHom, GradedTensorProduct.lift_tmul,
    map_one, one_mul]

end Left

/-! ### Strict commutation with the outer right action -/

section Right

variable {E : Type*} [Ring E] [Algebra K E]
variable [Module Eᵐᵒᵖ N] [SMulCommClass A Eᵐᵒᵖ N] [IsScalarTower K Eᵐᵒᵖ N]
variable [SMulCommClass C Eᵐᵒᵖ N]

/-- The signed middle action strictly commutes with the outer right
action (a closed-form computation — no parities enter). -/
theorem midEnd_comm_rightActionEnd (hsc : SuperCommSMul 𝒜 𝒞 N)
    (c : C) (e : Eᵐᵒᵖ) :
    midEnd 𝒜 ℳ 𝒞 hsc c * rightActionEnd K A M N e
      = rightActionEnd K A M N e * midEnd 𝒜 ℳ 𝒞 hsc c := by
  refine RelTensor.hom_ext fun m n => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, rightActionEnd_mk,
    midEnd_mk, midEnd_mk, midBilin_apply, midBilin_apply, map_sub,
    map_zsmul, rightActionEnd_mk, rightActionEnd_mk,
    smul_comm c e n, smul_comm (oddPart 𝒞 c) e n]

end Right

end Bimod

end Superfusion
