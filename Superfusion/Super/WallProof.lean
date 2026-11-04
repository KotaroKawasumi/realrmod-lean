/-
Superfusion / Super / WallProof

Milestone M4, parts 3–4: assembling **Wall's criterion**.

Part 3 (this file, first half): `A` as an honest module over the
enveloping superalgebra `E` via the Wall map (`wallModule`, a local
instance in the style of `TensorProduct.Algebra.module`), and the
translation of `RegularSimple.eq_bot_or_top_of_closed` into
`IsSimpleModule E A`.

Part 4 (second half): surjectivity of the Wall map from the Jacobson
density theorem (`Module.Finite.toModuleEnd_moduleEnd_surjective`), with
the commutant identified as the scalars by `RegularSchur`; injectivity by
the dimension count `dim E = (dim A)² = dim End_K A`.
-/
import Superfusion.Super.RegularSimple
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace Superfusion

open scoped TensorProduct

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]

/-! ### `A` as an `E`-module via the Wall map -/

theorem SuperOp.mulMap_one_left (x : A) : SuperOp.mulMap 𝒜 (1 : A) x = x := by
  rw [SuperOp.mulMap_apply, oddPart_of_mem_zero 𝒜 (SetLike.one_mem_graded 𝒜),
    mul_zero, smul_zero, sub_zero, mul_one]

/-- The regular `E`-module structure on `A`, through the Wall map.
A `def`, to be activated as a local instance. -/
noncomputable abbrev wallModule : Module (SuperEnvelope 𝒜) A :=
  Module.compHom A (superMulLeftRight 𝒜).toRingHom

section WallModule

attribute [local instance] wallModule

theorem wallModule_smul_def (e : SuperEnvelope 𝒜) (x : A) :
    e • x = superMulLeftRight 𝒜 e x := rfl

theorem wallModule_tmul_smul (a : A) (b : SuperOp 𝒜) (x : A) :
    ((a ᵍ⊗ₜ[K] b : SuperEnvelope 𝒜)) • x =
      a * SuperOp.mulMap 𝒜 (SuperOp.unop 𝒜 b) x := by
  rw [wallModule_smul_def, superMulLeftRight_tmul_apply]

theorem wallModule_lmul (a x : A) :
    ((a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜) : SuperEnvelope 𝒜)) • x = a * x := by
  rw [wallModule_tmul_smul,
    show SuperOp.unop 𝒜 (1 : SuperOp 𝒜) = (1 : A) from rfl,
    SuperOp.mulMap_one_left]

theorem wallModule_mulMap (b : A) (x : A) :
    (((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 b : SuperEnvelope 𝒜)) • x =
      SuperOp.mulMap 𝒜 b x := by
  rw [wallModule_tmul_smul, SuperOp.unop_op, one_mul]

theorem wallModule_algebraMap_smul (c : K) (x : A) :
    (algebraMap K (SuperEnvelope 𝒜) c) • x = c • x := by
  rw [wallModule_smul_def, AlgHom.commutes, Module.algebraMap_end_apply]

/-- The `K`-action factors through the `E`-action. -/
instance : IsScalarTower K (SuperEnvelope 𝒜) A where
  smul_assoc c e x := by
    rw [wallModule_smul_def, wallModule_smul_def, map_smul,
      LinearMap.smul_apply]

/-! ### Simplicity as an `E`-module -/

/-- **The regular bimodule is a simple `E`-module** (for a supercentral,
graded-simple superalgebra with `2` invertible). -/
theorem isSimpleModule_wall [Invertible (2 : K)] [IsGradedSimple 𝒜]
    [IsSuperCentral 𝒜] [Nontrivial A] :
    IsSimpleModule (SuperEnvelope 𝒜) A := by
  haveI hnt : Nontrivial (Submodule (SuperEnvelope 𝒜) A) :=
    ⟨⊥, ⊤, fun h => one_ne_zero (α := A) (by
      have h1 : (1 : A) ∈ (⊥ : Submodule (SuperEnvelope 𝒜) A) :=
        h ▸ Submodule.mem_top
      simp at h1)⟩
  refine { toNontrivial := hnt, eq_bot_or_eq_top := fun P => ?_ }
  -- restrict to a K-submodule closed under the two actions
  let Q : Submodule K A :=
    { carrier := P
      add_mem' := fun hx hy => P.add_mem hx hy
      zero_mem' := P.zero_mem
      smul_mem' := fun c x hx => by
        have h : c • x = (algebraMap K (SuperEnvelope 𝒜) c) • x :=
          (wallModule_algebraMap_smul 𝒜 c x).symm
        rw [h]
        exact P.smul_mem _ hx }
  have hmemQ : ∀ x : A, x ∈ Q ↔ x ∈ P := fun _ => Iff.rfl
  have hlQ : ∀ a : A, ∀ x ∈ Q, a * x ∈ Q := by
    intro a x hx
    rw [hmemQ] at hx ⊢
    rw [← wallModule_lmul 𝒜 a x]
    exact P.smul_mem _ hx
  have hrQ : ∀ b : A, ∀ x ∈ Q, SuperOp.mulMap 𝒜 b x ∈ Q := by
    intro b x hx
    rw [hmemQ] at hx ⊢
    rw [← wallModule_mulMap 𝒜 b x]
    exact P.smul_mem _ hx
  rcases eq_bot_or_top_of_closed 𝒜 Q hlQ hrQ with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    exact fun x hx => h x ((hmemQ x).mpr hx)
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    exact fun x => (hmemQ x).mp (h x)

/-! ### Surjectivity via Jacobson density -/

/-- `E`-scalars commute with `K`-scalars (the Wall action is `K`-linear). -/
instance : SMulCommClass (SuperEnvelope 𝒜) K A :=
  ⟨fun e c x => by rw [wallModule_smul_def, wallModule_smul_def, map_smul]⟩

/-- `E`-scalars commute with the commutant's action. -/
instance : SMulCommClass (SuperEnvelope 𝒜)
    (Module.End (SuperEnvelope 𝒜) A) A :=
  ⟨fun e φ x => (φ.map_smul e x).symm⟩

/-- The `K`-action factors through the commutant's action. -/
instance : IsScalarTower K (Module.End (SuperEnvelope 𝒜) A) A :=
  ⟨fun c φ x => by
    show (c • φ) x = c • φ x
    rw [LinearMap.smul_apply]⟩

/-- **The commutant is the scalars**: every `E`-linear endomorphism of the
regular bimodule is multiplication by an element of `K`
(via `RegularSchur`). -/
theorem end_wall_eq_smul [Invertible (2 : K)] [IsSuperCentral 𝒜]
    (φ : Module.End (SuperEnvelope 𝒜) A) : ∃ c : K, ∀ x : A, φ x = c • x := by
  let φK : Module.End K A :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun c x => by
        show φ (c • x) = c • φ x
        rw [← wallModule_algebraMap_smul 𝒜 c x, φ.map_smul,
          wallModule_algebraMap_smul] }
  have hl : ∀ a x : A, φK (a * x) = a * φK x := by
    intro a x
    show φ (a * x) = a * φ x
    rw [← wallModule_lmul 𝒜 a x, φ.map_smul, wallModule_lmul]
  have hr : ∀ b x : A, φK (SuperOp.mulMap 𝒜 b x) = SuperOp.mulMap 𝒜 b (φK x) := by
    intro b x
    show φ (SuperOp.mulMap 𝒜 b x) = SuperOp.mulMap 𝒜 b (φ x)
    rw [← wallModule_mulMap 𝒜 b x, φ.map_smul, wallModule_mulMap]
  obtain ⟨c, hc⟩ := exists_algebraMap_of_regular_comm 𝒜 φK hl hr
  refine ⟨c, fun x => ?_⟩
  have := congrArg (fun f : Module.End K A => f x) hc
  simpa [φK, Module.algebraMap_end_apply] using this

/-- **Surjectivity of the Wall map**, by Jacobson density: the commutant
is `K` (Schur), the module is simple, and `A` is finite over `K`. -/
theorem surjective_superMulLeftRight [Invertible (2 : K)] [IsGradedSimple 𝒜]
    [IsSuperCentral 𝒜] [Nontrivial A] [Module.Finite K A] :
    Function.Surjective (superMulLeftRight 𝒜) := by
  haveI := isSimpleModule_wall 𝒜
  haveI : Module.Finite (Module.End (SuperEnvelope 𝒜) A) A :=
    Module.Finite.of_restrictScalars_finite K _ _
  intro g
  -- lift g to a map linear over the commutant
  let ĝ : A →ₗ[Module.End (SuperEnvelope 𝒜) A] A :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := end_wall_eq_smul 𝒜 φ
        show g (φ x) = φ (g x)
        rw [hc, map_smul, hc] }
  obtain ⟨e, he⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
      (R := SuperEnvelope 𝒜) (M := A) ĝ
  refine ⟨e, LinearMap.ext fun x => ?_⟩
  have := congrArg (fun f : A →ₗ[Module.End (SuperEnvelope 𝒜) A] A => f x) he
  simpa [ĝ, wallModule_smul_def] using this

end WallModule

/-! ### Injectivity by dimension count, and Wall's criterion -/

section Field

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable [FiniteDimensional K A]

theorem finrank_superEnvelope :
    Module.finrank K (SuperEnvelope 𝒜) =
      Module.finrank K A * Module.finrank K A := by
  rw [← (GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜)).finrank_eq,
    Module.finrank_tensorProduct, (SuperOp.unop 𝒜).finrank_eq]

/-- **Wall's criterion, forward direction**: a finite-dimensional central
simple superalgebra over a field with `2 ≠ 0` is super-Azumaya — the Wall
map `E → End_K(A)` is bijective (paper eq. (2)). -/
theorem isSuperAzumaya_of_central_simple [Invertible (2 : K)]
    [IsGradedSimple 𝒜] [IsSuperCentral 𝒜] [Nontrivial A] :
    IsSuperAzumaya 𝒜 := by
  haveI : Module.Finite K (SuperOp 𝒜) := Module.Finite.equiv (SuperOp.op 𝒜)
  haveI : Module.Finite K (SuperEnvelope 𝒜) :=
    Module.Finite.equiv (GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜))
  have hsurj := surjective_superMulLeftRight 𝒜
  have hdim : Module.finrank K (SuperEnvelope 𝒜) =
      Module.finrank K (Module.End K A) := by
    rw [finrank_superEnvelope, Module.finrank_linearMap]
  refine ⟨⟨?_, hsurj⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (superMulLeftRight 𝒜).toLinearMap) hdim).mpr hsurj

end Field

end Superfusion
