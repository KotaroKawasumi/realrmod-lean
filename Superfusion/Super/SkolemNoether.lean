/-
Superfusion / Super / SkolemNoether

Milestone M6: **super Skolem–Noether** (Corollary 2.2), in the
uniqueness-and-parity form the paper uses downstream.

Given grade-preserving superalgebra maps `φ, φ' : A → B`, the target `B`
becomes an `(A,A)`-super-bimodule via the *twisted* actions
  `a • e = φ'(a) e`,   `e • b = e φ(b)`;
the supercenter of this bimodule is exactly the space of homogeneous
intertwiners `t` with
  `φ'(b) t = (-1)^{|b||t|} t φ(b)`.
When the twisted bimodule is irreducible, Proposition 2.1 gives:
the intertwiner space is **one-dimensional and concentrated in a single
parity** — the uniqueness (up to `K^×`) and well-defined parity of the
Skolem–Noether element.  (Existence of an *invertible* intertwiner for
`E` central simple — the remaining half of Corollary 2.2 — is future
work, via the semisimple decomposition of the twisted bimodule.)
-/
import Superfusion.Super.ParityConcentration

namespace Superfusion

section Twisted

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]

/-- A grade-preserving (super)algebra homomorphism. -/
def IsHomogeneousHom (φ : A →ₐ[K] B) : Prop :=
  ∀ i : ZMod 2, ∀ x ∈ 𝒜 i, φ x ∈ ℬ i

variable (φ φ' : A →ₐ[K] B)

/-- Type synonym: `B` as an `(A,A)`-super-bimodule via the twisted actions
`a • e • b = φ'(a) e φ(b)`. -/
@[nolint unusedArguments]
def Twisted (φ φ' : A →ₐ[K] B) (_ : IsHomogeneousHom 𝒜 ℬ φ)
    (_ : IsHomogeneousHom 𝒜 ℬ φ') : Type _ := B

variable (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')

namespace Twisted

instance : AddCommGroup (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (AddCommGroup B)

instance : Module K (Twisted 𝒜 ℬ φ φ' hφ hφ') := inferInstanceAs (Module K B)

/-- Interpret an element of `B` in the twisted bimodule. -/
def of : B ≃ₗ[K] Twisted 𝒜 ℬ φ φ' hφ hφ' := LinearEquiv.refl K B

instance : Module B (Twisted 𝒜 ℬ φ φ' hφ hφ') := inferInstanceAs (Module B B)

instance : Module Bᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (Module Bᵐᵒᵖ B)

/-- The twisted left action `a • e = φ'(a) e`. -/
instance : Module A (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  Module.compHom (Twisted 𝒜 ℬ φ φ' hφ hφ') φ'.toRingHom

/-- The twisted right action `(op a) • e = e φ(a)`. -/
instance : Module Aᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  Module.compHom (Twisted 𝒜 ℬ φ φ' hφ hφ') (RingHom.op φ.toRingHom)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem smul_def (a : A) (e : B) :
    a • of 𝒜 ℬ φ φ' hφ hφ' e = of 𝒜 ℬ φ φ' hφ hφ' (φ' a * e) := rfl

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem op_smul_def (a : A) (e : B) :
    MulOpposite.op a • of 𝒜 ℬ φ φ' hφ hφ' e =
      of 𝒜 ℬ φ φ' hφ hφ' (e * φ a) := rfl

instance : SMulCommClass B Bᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (SMulCommClass B Bᵐᵒᵖ B)

instance : IsScalarTower K B (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (IsScalarTower K B B)

instance : IsScalarTower K Bᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (IsScalarTower K Bᵐᵒᵖ B)

instance : SMulCommClass A Aᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  ⟨fun a b e => smul_comm (φ' a) ((RingHom.op φ.toRingHom) b) e⟩

instance : IsScalarTower K A (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  ⟨fun c a e => by
    show (φ' (c • a) : B) • e = c • ((φ' a : B) • e)
    rw [map_smul, smul_assoc]⟩

instance : IsScalarTower K Aᵐᵒᵖ (Twisted 𝒜 ℬ φ φ' hφ hφ') :=
  ⟨fun c a e => by
    show ((RingHom.op φ.toRingHom) (c • a)) • e =
      c • (((RingHom.op φ.toRingHom) a) • e)
    have hop : (RingHom.op φ.toRingHom) (c • a) =
        c • (RingHom.op φ.toRingHom) a := by
      show MulOpposite.op (φ ((c • a).unop)) = _
      rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul]
      rfl
    rw [hop, smul_assoc]⟩

/-- The grading of the twisted bimodule (the grading of `B`). -/
def grading : ZMod 2 → Submodule K (Twisted 𝒜 ℬ φ φ' hφ hφ') := ℬ

instance : DirectSum.Decomposition (grading 𝒜 ℬ φ φ' hφ hφ') :=
  inferInstanceAs (DirectSum.Decomposition ℬ)

instance : SetLike.GradedSMul 𝒜 (grading 𝒜 ℬ φ φ' hφ hφ') :=
  ⟨fun {i j} {a e} ha he => by
    have he' : (of 𝒜 ℬ φ φ' hφ hφ').symm e ∈ ℬ j := he
    have h := SetLike.mul_mem_graded (hφ' i a ha) he'
    exact h⟩

instance : GradedRightSMul 𝒜 (grading 𝒜 ℬ φ φ' hφ hφ') :=
  ⟨fun {i j} a e ha he => by
    have he' : (of 𝒜 ℬ φ φ' hφ hφ').symm e ∈ ℬ j := he
    have h := SetLike.mul_mem_graded he' (hφ i a ha)
    rw [add_comm j i] at h
    exact h⟩

end Twisted

/-- Elements of the supercenter of the twisted bimodule **intertwine**
`φ` and `φ'` with the Koszul sign: for homogeneous `t` of parity `k` and
`b ∈ 𝒜 j`,
  `φ'(b) t = (-1)^{jk} t φ(b)`. -/
theorem intertwines_of_mem_superCenterBimod {t : B}
    (ht : Twisted.of 𝒜 ℬ φ φ' hφ hφ' t ∈
      superCenterBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ'))
    {k : ZMod 2} (htk : t ∈ ℬ k) {j : ZMod 2} {b : A} (hb : b ∈ 𝒜 j) :
    φ' b * t = ((sgn (j * k) : ℤˣ) : ℤ) • (t * φ b) := by
  have h := (mem_superCenterBimod 𝒜 _).mp ht b
  rw [signedRSMul_of_mem 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') hb
    (show Twisted.of 𝒜 ℬ φ φ' hφ hφ' t ∈ Twisted.grading 𝒜 ℬ φ φ' hφ hφ' k
      from htk)] at h
  exact h

end Twisted

/-! ### Super Skolem–Noether, uniqueness and parity -/

section Main

variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra ℬ]
variable (φ φ' : A →ₐ[K] B)
variable (hφ : IsHomogeneousHom 𝒜 ℬ φ) (hφ' : IsHomogeneousHom 𝒜 ℬ φ')
variable [Invertible (2 : K)] [FiniteDimensional K A] [Nontrivial A]
variable [IsSuperCentral 𝒜] [IsGradedSimple 𝒜]

/-- **Super Skolem–Noether** (Corollary 2.2, uniqueness and parity): if the
`(φ,φ')`-twisted bimodule is irreducible, the space of intertwiners
`{t | φ'(b) t = (-1)^{|b||t|} t φ(b)}` is one-dimensional and concentrated
in a single parity — the Skolem–Noether element is unique up to `K^×` and
has a well-defined parity. -/
theorem superSkolemNoether_unique
    (hirr : IsSimpleSuperBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')) :
    Module.finrank K
        (superCenterBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ')) = 1 ∧
      ∃ i : ZMod 2,
        superCenterBimod 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') ≤
          Twisted.grading 𝒜 ℬ φ φ' hφ hφ' i :=
  prop21 𝒜 (Twisted.grading 𝒜 ℬ φ φ' hφ hφ') hirr

end Main

end Superfusion
