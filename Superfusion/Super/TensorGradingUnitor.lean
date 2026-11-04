/-
Superfusion / Super / TensorGradingUnitor

Milestone M7f-4a: **the unitors of the graded tensor product, and the
bundled operations** —

  `gunitorRight : 𝒜 ᵍ⊗ (evenGrading K K) ≃ₐ A`,
  `gunitorLeft  : (evenGrading K K) ᵍ⊗ 𝒜 ≃ₐ A`,

both carrying gradings onto gradings (the scalar factor is purely
even, so no Koszul sign appears anywhere), plus the bundled
`SuperAlgebra.gtensor` and `SuperAlgebra.sop` with their
`SuperAlgEquiv` unitors.

Together with associativity (M7f-1c), the braiding (M7f-1g), the
super-Azumaya closure (M7f-2) and the graded Wall isomorphism
(M7f-2a), these are the structure maps of the Brauer–Wall monoid;
M7f-4 assembles the group.
-/
import Superfusion.Super.TensorGradingComm
import Superfusion.Super.TensorGradingSop
import Superfusion.Super.BWPeriodicity

namespace Superfusion

open TensorProduct
open GradedTensorProduct

section Unitor

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

private theorem ksmul_gtmul (c : K) (x : A) (y : K) :
    ((c • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] evenGrading K K)
      = c • (x ᵍ⊗ₜ[K] y) := by
  rw [show (((c • x) ᵍ⊗ₜ[K] y : 𝒜 ᵍ⊗[K] evenGrading K K))
      = of K 𝒜 (evenGrading K K) ((c • x) ⊗ₜ[K] y) from rfl,
    show ((c • x) ⊗ₜ[K] y : A ⊗[K] K) = c • (x ⊗ₜ[K] y) from
      (TensorProduct.smul_tmul' _ _ _).symm,
    map_smul]

private theorem gtmul_ksmul (c : K) (x : A) (y : K) :
    (x ᵍ⊗ₜ[K] (c • y) : 𝒜 ᵍ⊗[K] evenGrading K K)
      = c • (x ᵍ⊗ₜ[K] y) := by
  rw [show ((x ᵍ⊗ₜ[K] (c • y) : 𝒜 ᵍ⊗[K] evenGrading K K))
      = of K 𝒜 (evenGrading K K) (x ⊗ₜ[K] (c • y)) from rfl,
    TensorProduct.tmul_smul, map_smul]

private theorem mem_evenGrading_one {k : K}
    (h : k ∈ evenGrading K K 1) : k = 0 := by
  rw [show evenGrading K K 1 = ⊥ from by
    rw [evenGrading]
    exact if_neg one_ne_zero] at h
  exact (Submodule.mem_bot K).mp h

omit [GradedAlgebra 𝒜] in
private theorem unitor_anticommutes :
    ∀ ⦃i j : ZMod 2⦄ (a : 𝒜 i) (k : evenGrading K K j),
      (AlgHom.id K A) a * (Algebra.ofId K A) k
        = (-1 : ℤˣ) ^ (j * i) •
          ((Algebra.ofId K A) k * (AlgHom.id K A) a) := by
  intro i j a k
  rcases zmod2_cases j with hj | hj <;> subst hj
  · rw [show (Algebra.ofId K A) (k : K) = algebraMap K A k from rfl,
      show (AlgHom.id K A) (a : A) = (a : A) from rfl,
      Algebra.commutes, zero_mul, uzpow_zero, one_smul]
  · rw [show (Algebra.ofId K A) (k : K) = algebraMap K A k from rfl,
      mem_evenGrading_one k.2, map_zero, mul_zero, zero_mul,
      smul_zero]

/-- The algebra map `𝒜 ᵍ⊗ (evenGrading K K) → A`,
`a ᵍ⊗ k ↦ a · k`. -/
noncomputable def gunitorRightHom :
    (𝒜 ᵍ⊗[K] evenGrading K K) →ₐ[K] A :=
  lift 𝒜 (evenGrading K K) (AlgHom.id K A) (Algebra.ofId K A)
    (unitor_anticommutes 𝒜)

theorem gunitorRightHom_tmul (a : A) (k : K) :
    gunitorRightHom 𝒜 (a ᵍ⊗ₜ[K] k) = a * algebraMap K A k :=
  lift_tmul 𝒜 (evenGrading K K) (AlgHom.id K A) (Algebra.ofId K A)
    (unitor_anticommutes 𝒜) a k

/-- **The right unitor** (M7f-4a):
`𝒜 ᵍ⊗ (evenGrading K K) ≃ₐ A`, `a ᵍ⊗ k ↦ a · k`. -/
noncomputable def gunitorRight :
    (𝒜 ᵍ⊗[K] evenGrading K K) ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (gunitorRightHom 𝒜)
    (includeLeft 𝒜 (evenGrading K K))
    (AlgHom.ext fun a => by
      show gunitorRightHom 𝒜 (a ᵍ⊗ₜ[K] (1 : K)) = a
      rw [gunitorRightHom_tmul, map_one, mul_one])
    (galgHom_ext 𝒜 (evenGrading K K) fun a k => by
      show includeLeft 𝒜 (evenGrading K K)
          (gunitorRightHom 𝒜 (a ᵍ⊗ₜ[K] k)) = a ᵍ⊗ₜ[K] k
      rw [gunitorRightHom_tmul,
        show includeLeft 𝒜 (evenGrading K K) (a * algebraMap K A k)
          = (a * algebraMap K A k) ᵍ⊗ₜ[K] (1 : K) from rfl,
        show a * algebraMap K A k = k • a from by
          rw [← Algebra.commutes, ← Algebra.smul_def],
        ksmul_gtmul,
        show (a ᵍ⊗ₜ[K] k : 𝒜 ᵍ⊗[K] evenGrading K K)
          = a ᵍ⊗ₜ[K] (k • (1 : K)) from by
          rw [smul_eq_mul, mul_one],
        gtmul_ksmul])

theorem gunitorRightHom_isHomogeneous :
    IsHomogeneousHom (tensorGrading 𝒜 (evenGrading K K)) 𝒜
      (gunitorRightHom 𝒜) := by
  intro i z hz
  refine tensorGrading_induction 𝒜 (evenGrading K K) hz
    (p := fun w => gunitorRightHom 𝒜 w ∈ 𝒜 i) ?_ ?_ ?_ ?_
  · intro j l x y hjl hx hy
    rw [gunitorRightHom_tmul]
    rcases zmod2_cases l with hl | hl <;> subst hl
    · rw [show x * algebraMap K A y = y • x from by
        rw [← Algebra.commutes, ← Algebra.smul_def]]
      have h := Submodule.smul_mem (𝒜 j) y hx
      rwa [show j = i from by rw [← hjl, add_zero]] at h
    · rw [mem_evenGrading_one hy, map_zero, mul_zero]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro u v hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro c u hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- The right unitor carries the tensor grading **onto** the
grading. -/
theorem gunitorRight_map_grading (i : ZMod 2) :
    (tensorGrading 𝒜 (evenGrading K K) i).map
        (gunitorRight 𝒜).toLinearMap
      = 𝒜 i :=
  map_grading_of_bijective (tensorGrading 𝒜 (evenGrading K K)) 𝒜
    (gunitorRightHom 𝒜) (gunitorRightHom_isHomogeneous 𝒜)
    (gunitorRight 𝒜).bijective i

/-- **The left unitor**: `(evenGrading K K) ᵍ⊗ 𝒜 ≃ₐ A`. -/
noncomputable def gunitorLeft :
    (evenGrading K K ᵍ⊗[K] 𝒜) ≃ₐ[K] A :=
  (comm (evenGrading K K) 𝒜).trans (gunitorRight 𝒜)

/-- The left graded tensor unitor sends a pure tensor to scalar
multiplication.  The scalar factor is purely even, so the braiding used in
the definition of `gunitorLeft` contributes no Koszul sign. -/
theorem gunitorLeft_tmul (k : K) (x : A) :
    gunitorLeft 𝒜 (k ᵍ⊗ₜ[K] x) = k • x := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
      change gunitorLeft 𝒜
          (of K (evenGrading K K) 𝒜
            (k ⊗ₜ[K] (0 : A))) =
        k • (0 : A)
      rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
  | add x y hx hy =>
      change gunitorLeft 𝒜
          (of K (evenGrading K K) 𝒜
            (k ⊗ₜ[K] (x + y))) =
        k • (x + y)
      rw [TensorProduct.tmul_add, map_add, map_add, hx, hy, smul_add]
  | @homogeneous i x =>
      rw [gunitorLeft, AlgEquiv.trans_apply]
      let k0 : evenGrading K K 0 :=
        ⟨k, mem_evenGrading_zero K K k⟩
      change gunitorRight 𝒜
          (comm (evenGrading K K) 𝒜
            ((k0 : K) ᵍ⊗ₜ[K] (x : A))) =
        k • (x : A)
      rw [comm_coe_tmul_coe, mul_zero, uzpow_zero, one_smul]
      change gunitorRightHom 𝒜
          ((x : A) ᵍ⊗ₜ[K] k) =
        k • (x : A)
      rw [gunitorRightHom_tmul]
      rw [← Algebra.commutes, ← Algebra.smul_def]

theorem gunitorLeft_map_grading (i : ZMod 2) :
    (tensorGrading (evenGrading K K) 𝒜 i).map
        (gunitorLeft 𝒜).toLinearMap
      = 𝒜 i :=
  map_grading_trans _ _ _ (comm (evenGrading K K) 𝒜) (gunitorRight 𝒜)
    (comm_map_grading (evenGrading K K) 𝒜)
    (gunitorRight_map_grading 𝒜) i

end Unitor

/-! ### Bundled operations -/

section Bundled

variable {K : Type*} [CommRing K]

/-- The graded tensor product of bundled superalgebras. -/
noncomputable def SuperAlgebra.gtensor (P Q : SuperAlgebra K) :
    SuperAlgebra K where
  carrier := P.grading ᵍ⊗[K] Q.grading
  grading := tensorGrading P.grading Q.grading

/-- The super-opposite of a bundled superalgebra. -/
noncomputable def SuperAlgebra.sop (P : SuperAlgebra K) :
    SuperAlgebra K where
  carrier := SuperOp P.grading
  grading := SuperOp.grading P.grading

/-- The bundled right unitor: `P ᵍ⊗ K ≅ P`. -/
noncomputable def gtensorUnitorRight (P : SuperAlgebra K) :
    SuperAlgEquiv (P.gtensor (SuperAlgebra.base K)) P :=
  ⟨gunitorRight P.grading, gunitorRight_map_grading P.grading⟩

/-- The bundled right unitor sends a pure tensor to scalar
multiplication. -/
@[simp]
theorem gtensorUnitorRight_tmul (P : SuperAlgebra K)
    (x : P.carrier) (k : K) :
    (gtensorUnitorRight P).toAlgEquiv
        (show P.grading ᵍ⊗[K] (SuperAlgebra.base K).grading from
          x ᵍ⊗ₜ[K] k) =
      k • x := by
  change gunitorRightHom P.grading (x ᵍ⊗ₜ[K] k) = k • x
  rw [gunitorRightHom_tmul, ← Algebra.commutes, ← Algebra.smul_def]

/-- The bundled left unitor: `K ᵍ⊗ P ≅ P`. -/
noncomputable def gtensorUnitorLeft (P : SuperAlgebra K) :
    SuperAlgEquiv ((SuperAlgebra.base K).gtensor P) P :=
  ⟨gunitorLeft P.grading, gunitorLeft_map_grading P.grading⟩

/-- The bundled left unitor sends a pure tensor to scalar
multiplication. -/
@[simp]
theorem gtensorUnitorLeft_tmul (P : SuperAlgebra K)
    (k : K) (x : P.carrier) :
    (gtensorUnitorLeft P).toAlgEquiv
        (show (SuperAlgebra.base K).grading ᵍ⊗[K] P.grading from
          k ᵍ⊗ₜ[K] x) =
      k • x :=
  gunitorLeft_tmul P.grading k x

end Bundled

end Superfusion
