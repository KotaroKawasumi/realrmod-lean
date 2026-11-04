/-
Superfusion / Super / Prop21

Milestone M5 (Proposition 2.1), dimension half: **the supercenter of an
irreducible super-bimodule over a central simple superalgebra is
one-dimensional**.

Route: `E = A ⊗̂ A^sop` is a simple Artinian ring (Wall's criterion makes
it `≃ End_K(A)`, a matrix algebra); over a simple Artinian ring every
module is isotypic, so the two simple `E`-modules `A` (regular, by
`RegularSimple`) and `M` (irreducibility) are `E`-equivalent; the
supercenter is transferred along the equivalence
(`SuperCenterBimod.map_superCenterBimod`), and on the regular bimodule it
is `K·1` of dimension 1.

Parity concentration (the other half of Proposition 2.1) is next.
-/
import Superfusion.Super.SuperCenterBimod
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Superfusion

open scoped TensorProduct

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable [Invertible (2 : K)] [FiniteDimensional K A] [Nontrivial A]
variable [IsSuperCentral 𝒜] [IsGradedSimple 𝒜]

/-- The enveloping superalgebra of a central simple superalgebra is a
simple ring (via Wall's criterion and simplicity of matrix algebras). -/
theorem isSimpleRing_superEnvelope : IsSimpleRing (SuperEnvelope 𝒜) := by
  haveI : Nonempty (Fin (Module.finrank K A)) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  haveI : IsSimpleRing (Module.End K A) :=
    IsSimpleRing.of_ringEquiv
      (algEquivMatrix (Module.finBasis K A)).symm.toRingEquiv inferInstance
  exact IsSimpleRing.of_ringEquiv
    (RingEquiv.ofBijective (superMulLeftRight 𝒜).toRingHom
      (isSuperAzumaya_of_central_simple 𝒜).bij).symm inferInstance

section Irreducible

variable {M : Type*} [AddCommGroup M] [Module K M]
variable (ℳ : ZMod 2 → Submodule K M) [DirectSum.Decomposition ℳ]
variable [Module A M] [Module Aᵐᵒᵖ M]
variable [SMulCommClass A Aᵐᵒᵖ M] [IsScalarTower K A M] [IsScalarTower K Aᵐᵒᵖ M]
variable [SetLike.GradedSMul 𝒜 ℳ] [GradedRightSMul 𝒜 ℳ]

/-- Irreducibility of a super-bimodule, instance-free: nontrivial, with no
proper nonzero submodules closed under the left action and the signed
right action. -/
structure IsSimpleSuperBimod : Prop where
  nontrivial : Nontrivial M
  eq_bot_or_top : ∀ N : Submodule K M,
    (∀ a : A, ∀ x ∈ N, a • x ∈ N) →
    (∀ b : A, ∀ x ∈ N, signedRSMul 𝒜 ℳ b x ∈ N) →
    N = ⊥ ∨ N = ⊤

/-- **Proposition 2.1, dimension half**: the supercenter of an irreducible
super-bimodule over a central simple superalgebra is one-dimensional. -/
theorem finrank_superCenterBimod_of_simple (hM : IsSimpleSuperBimod 𝒜 ℳ) :
    Module.finrank K (superCenterBimod 𝒜 ℳ) = 1 := by
  letI instEM : Module (SuperEnvelope 𝒜) M := SuperBimodule.module 𝒜 ℳ
  letI instEA : Module (SuperEnvelope 𝒜) A := wallModule 𝒜
  haveI := hM.nontrivial
  have hsmulM : ∀ (e : SuperEnvelope 𝒜) (m : M),
      e • m = superBimoduleAlgHom 𝒜 ℳ e m := fun _ _ => rfl
  have hsmulA : ∀ (e : SuperEnvelope 𝒜) (x : A),
      e • x = superBimoduleAlgHom 𝒜 𝒜 e x := by
    intro e x
    rw [superBimoduleAlgHom_self]
    rfl
  -- towers over K (needed to restrict scalars)
  letI : IsScalarTower K (SuperEnvelope 𝒜) M :=
    ⟨fun c e m => by rw [hsmulM, hsmulM, map_smul, LinearMap.smul_apply]⟩
  -- M is a simple E-module
  haveI hntM : Nontrivial (Submodule (SuperEnvelope 𝒜) M) := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    refine ⟨⊥, ⊤, fun h => hm ?_⟩
    have : m ∈ (⊥ : Submodule (SuperEnvelope 𝒜) M) := h ▸ Submodule.mem_top
    simpa using this
  haveI hsimpleM : IsSimpleModule (SuperEnvelope 𝒜) M := by
    refine { toNontrivial := hntM, eq_bot_or_eq_top := fun P => ?_ }
    let Q : Submodule K M :=
      { carrier := P
        add_mem' := fun hx hy => P.add_mem hx hy
        zero_mem' := P.zero_mem
        smul_mem' := fun c x hx => by
          have h : c • x = (algebraMap K (SuperEnvelope 𝒜) c) • x := by
            rw [hsmulM, AlgHom.commutes, Module.algebraMap_end_apply]
          rw [h]
          exact P.smul_mem _ hx }
    have hmemQ : ∀ x : M, x ∈ Q ↔ x ∈ P := fun _ => Iff.rfl
    have hlQ : ∀ a : A, ∀ x ∈ Q, a • x ∈ Q := by
      intro a x hx
      rw [hmemQ] at hx ⊢
      have h : a • x =
          ((a ᵍ⊗ₜ[K] (1 : SuperOp 𝒜) : SuperEnvelope 𝒜)) • x := by
        rw [hsmulM, superBimoduleAlgHom_lmul_one]
      rw [h]
      exact P.smul_mem _ hx
    have hrQ : ∀ b : A, ∀ x ∈ Q, signedRSMul 𝒜 ℳ b x ∈ Q := by
      intro b x hx
      rw [hmemQ] at hx ⊢
      have h : signedRSMul 𝒜 ℳ b x =
          (((1 : A) ᵍ⊗ₜ[K] SuperOp.op 𝒜 b : SuperEnvelope 𝒜)) • x := by
        rw [hsmulM, superBimoduleAlgHom_one_op]
      rw [h]
      exact P.smul_mem _ hx
    rcases hM.eq_bot_or_top Q hlQ hrQ with h | h
    · left
      rw [Submodule.eq_bot_iff] at h ⊢
      exact fun x hx => h x ((hmemQ x).mpr hx)
    · right
      rw [Submodule.eq_top_iff'] at h ⊢
      exact fun x => (hmemQ x).mp (h x)
  -- A is a simple E-module (M4)
  haveI hsimpleA : IsSimpleModule (SuperEnvelope 𝒜) A := isSimpleModule_wall 𝒜
  -- E is simple Artinian
  haveI := isSimpleRing_superEnvelope 𝒜
  haveI : Module.Finite K (SuperOp 𝒜) := Module.Finite.equiv (SuperOp.op 𝒜)
  haveI : Module.Finite K (SuperEnvelope 𝒜) :=
    Module.Finite.equiv (GradedTensorProduct.of K 𝒜 (SuperOp.grading 𝒜))
  haveI : IsArtinianRing (SuperEnvelope 𝒜) := IsArtinianRing.of_finite K _
  -- the E-equivalence A ≃ M by isotypicity of A × M
  obtain ⟨φ⟩ : Nonempty (A ≃ₗ[SuperEnvelope 𝒜] M) := by
    haveI h1 : IsSimpleModule (SuperEnvelope 𝒜)
        (Submodule.fst (SuperEnvelope 𝒜) A M) :=
      (Submodule.fstEquiv (SuperEnvelope 𝒜) A M).isSimpleModule_iff.mpr
        hsimpleA
    haveI h2 : IsSimpleModule (SuperEnvelope 𝒜)
        (Submodule.snd (SuperEnvelope 𝒜) A M) :=
      (Submodule.sndEquiv (SuperEnvelope 𝒜) A M).isSimpleModule_iff.mpr
        hsimpleM
    obtain ⟨e⟩ := IsSimpleRing.isIsotypic (R := SuperEnvelope 𝒜) (A × M)
      (Submodule.snd (SuperEnvelope 𝒜) A M)
      (Submodule.fst (SuperEnvelope 𝒜) A M)
    exact ⟨((Submodule.fstEquiv (SuperEnvelope 𝒜) A M).symm.trans e).trans
      (Submodule.sndEquiv (SuperEnvelope 𝒜) A M)⟩
  -- equivariance in algebra-action form
  have hφ : ∀ (e : SuperEnvelope 𝒜) (x : A),
      φ (superBimoduleAlgHom 𝒜 𝒜 e x) = superBimoduleAlgHom 𝒜 ℳ e (φ x) := by
    intro e x
    rw [← hsmulA, ← hsmulM, map_smul]
  have hφ' : ∀ (e : SuperEnvelope 𝒜) (m : M),
      φ.symm (superBimoduleAlgHom 𝒜 ℳ e m) =
        superBimoduleAlgHom 𝒜 𝒜 e (φ.symm m) := by
    intro e m
    rw [← hsmulA, ← hsmulM, map_smul]
  -- the supercenters correspond
  let φK : A ≃ₗ[K] M := φ.restrictScalars K
  have hmap : (superCenterBimod 𝒜 𝒜).map (φK : A →ₗ[K] M) =
      superCenterBimod 𝒜 ℳ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact map_superCenterBimod 𝒜 ℳ (φK : A →ₗ[K] M) hφ hx
    · intro m hm
      refine ⟨φ.symm m, ?_, by simp [φK]⟩
      show φ.symm m ∈ superCenterBimod 𝒜 𝒜
      rw [mem_superCenterBimod_iff_E] at hm ⊢
      intro b
      have h2 := congrArg φ.symm (hm b)
      rw [hφ', hφ'] at h2
      exact h2
  rw [← hmap, LinearEquiv.finrank_map_eq]
  exact finrank_superCenterBimod_regular 𝒜

end Irreducible

end Superfusion
