/-
Superfusion / Super / Basic

Superalgebras (§2.1), first definitions.  A superalgebra over `K` is a
`ZMod 2`-graded associative unital `K`-algebra, encoded mathlib-style as
`GradedAlgebra (𝒜 : ZMod 2 → Submodule K A)` (the same idiom as
`CliffordAlgebra.gradedAlgebra`).

This file fixes the two basic predicates of the paper's §2.1:

* the supercenter `Ẑ(A) = {a homogeneous : ab = (-1)^{|a||b|} ba ∀ b}`
  (as a `Submodule K A`, the span of its homogeneous layers);
* graded simplicity (no nontrivial homogeneous two-sided ideals);
* their conjunction, "central simple superalgebra", as two mixin classes
  `IsSuperCentral` and `IsGradedSimple`.

Wall's criterion (eq. (2): `A ⊗̂ Aˢᵒᵖ ≅ End(A)`), the super-opposite,
and matrix superalgebras `M_γ(D)` come next; Proposition 2.1 and super
Skolem–Noether (Corollary 2.2) are the goals of this track.

Sign convention: all Koszul signs route through `sgn : ZMod 2 → ℤˣ`
(Conventions.lean) acting by `ℤ`-scalars, so the definitions make sense
over any commutative base ring, and in characteristic 2 they degenerate
to the ungraded notions, as they must.
-/
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.SimpleRing.Defs
import Superfusion.Conventions

namespace Superfusion

variable {K : Type*} [CommRing K] {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A)

/-! ### Supercommutation and the supercenter -/

/-- `a` supercommutes in degree `i`: `a * b = (-1)^{i·j} (b * a)` for every
homogeneous `b` of degree `j`.  (Membership of `a` in `𝒜 i` is tracked
separately, in `superCenterGrade`.) -/
def IsSupercentral (i : ZMod 2) (a : A) : Prop :=
  ∀ j : ZMod 2, ∀ b ∈ 𝒜 j, a * b = ((sgn (i * j) : ℤˣ) : ℤ) • (b * a)

theorem isSupercentral_zero (i : ZMod 2) : IsSupercentral 𝒜 i 0 := by
  intro j b _
  simp

theorem IsSupercentral.add {i : ZMod 2} {a a' : A}
    (ha : IsSupercentral 𝒜 i a) (ha' : IsSupercentral 𝒜 i a') :
    IsSupercentral 𝒜 i (a + a') := by
  intro j b hb
  rw [add_mul, ha j b hb, ha' j b hb, mul_add, smul_add]

theorem IsSupercentral.smul {i : ZMod 2} {a : A} (c : K)
    (ha : IsSupercentral 𝒜 i a) : IsSupercentral 𝒜 i (c • a) := by
  intro j b hb
  rw [smul_mul_assoc, ha j b hb, mul_smul_comm, smul_comm]

/-- Supercentral elements are closed under multiplication (with additive
degrees), so the supercenter is a subalgebra. -/
theorem IsSupercentral.mul {i i' : ZMod 2} {a a' : A}
    (ha : IsSupercentral 𝒜 i a) (ha' : IsSupercentral 𝒜 i' a') :
    IsSupercentral 𝒜 (i + i') (a * a') := by
  intro j b hb
  have hsgn : (((sgn (i' * j) : ℤˣ) : ℤ)) * ((sgn (i * j) : ℤˣ) : ℤ) =
      ((sgn ((i + i') * j) : ℤˣ) : ℤ) := by
    rw [← Units.val_mul, ← sgn_add]
    congr 1
    ring
  calc a * a' * b
      = a * (a' * b) := by rw [mul_assoc]
    _ = ((sgn (i' * j) : ℤˣ) : ℤ) • (a * (b * a')) := by
        rw [ha' j b hb, mul_smul_comm]
    _ = ((sgn (i' * j) : ℤˣ) : ℤ) • (a * b * a') := by rw [mul_assoc]
    _ = ((sgn (i' * j) : ℤˣ) : ℤ) •
          ((((sgn (i * j) : ℤˣ) : ℤ) • (b * a)) * a') := by rw [ha j b hb]
    _ = ((sgn ((i + i') * j) : ℤˣ) : ℤ) • (b * (a * a')) := by
        rw [smul_mul_assoc, smul_smul, hsgn, mul_assoc]

/-- The degree-`i` layer of the supercenter. -/
def superCenterGrade (i : ZMod 2) : Submodule K A where
  carrier := {a | a ∈ 𝒜 i ∧ IsSupercentral 𝒜 i a}
  zero_mem' := ⟨zero_mem _, isSupercentral_zero 𝒜 i⟩
  add_mem' ha ha' := ⟨add_mem ha.1 ha'.1, ha.2.add 𝒜 ha'.2⟩
  smul_mem' c _ ha := ⟨Submodule.smul_mem _ c ha.1, ha.2.smul 𝒜 c⟩

/-- The supercenter `Ẑ(A)` of a superalgebra (§2.1): the span of the
homogeneous supercentral elements. -/
def superCenter : Submodule K A :=
  superCenterGrade 𝒜 0 ⊔ superCenterGrade 𝒜 1

/-- Scalars are even and supercentral, so the unit subalgebra always lies
in the supercenter. -/
theorem one_le_superCenter [GradedAlgebra 𝒜] :
    (1 : Submodule K A) ≤ superCenter 𝒜 := by
  rw [Submodule.one_eq_span, Submodule.span_le, Set.singleton_subset_iff]
  refine le_sup_left (a := superCenterGrade 𝒜 0) ?_
  refine ⟨SetLike.one_mem_graded 𝒜, fun j b _ => ?_⟩
  simp [zero_mul]

/-! ### Central simple superalgebras -/

/-- A superalgebra is supercentral if its supercenter is exactly the
scalars.  (The inclusion `⊇` is automatic: `one_le_superCenter`.) -/
class IsSuperCentral [GradedAlgebra 𝒜] : Prop where
  superCenter_le_one : superCenter 𝒜 ≤ 1

theorem superCenter_eq_one [GradedAlgebra 𝒜] [IsSuperCentral 𝒜] :
    superCenter 𝒜 = 1 :=
  le_antisymm IsSuperCentral.superCenter_le_one (one_le_superCenter 𝒜)

/-- A two-sided ideal is homogeneous if it is stable under taking graded
components. -/
def TwoSidedIdeal.IsHomogeneous [GradedAlgebra 𝒜] (I : TwoSidedIdeal A) : Prop :=
  ∀ a ∈ I, ∀ i : ZMod 2, ((DirectSum.decompose 𝒜 a) i : A) ∈ I

/-- A superalgebra is graded-simple if it has no homogeneous two-sided
ideals besides `⊥` and `⊤` (§2.1). -/
class IsGradedSimple [GradedAlgebra 𝒜] : Prop where
  eq_bot_or_eq_top :
    ∀ I : TwoSidedIdeal A, TwoSidedIdeal.IsHomogeneous 𝒜 I → I = ⊥ ∨ I = ⊤

/-- A simple ring is graded-simple for every grading. -/
theorem isGradedSimple_of_isSimpleRing [GradedAlgebra 𝒜] [IsSimpleRing A] :
    IsGradedSimple 𝒜 :=
  ⟨fun I _ => eq_bot_or_eq_top I⟩

/-- **Central simple superalgebra** (§2.1): supercentral and graded-simple.
Bundled as a conjunction of the two mixins for readability at use sites. -/
abbrev IsCentralSimpleSuper [GradedAlgebra 𝒜] : Prop :=
  IsSuperCentral 𝒜 ∧ IsGradedSimple 𝒜

/-- A homogeneous supercentral element of a supercentral superalgebra is a
scalar. -/
theorem mem_one_of_isSupercentral [GradedAlgebra 𝒜] [IsSuperCentral 𝒜]
    {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) (hac : IsSupercentral 𝒜 i a) :
    a ∈ (1 : Submodule K A) := by
  refine IsSuperCentral.superCenter_le_one (𝒜 := 𝒜) ?_
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact le_sup_left (α := Submodule K A) ⟨ha, hac⟩
  · exact le_sup_right (α := Submodule K A) ⟨ha, hac⟩

/-! ### Elementary consequences -/

/-- In degree 0, supercommutation is plain commutation with homogeneous
elements. -/
theorem isSupercentral_zero_iff (a : A) :
    IsSupercentral 𝒜 0 a ↔ ∀ j : ZMod 2, ∀ b ∈ 𝒜 j, a * b = b * a := by
  constructor
  · intro h j b hb
    have := h j b hb
    simpa using this
  · intro h j b hb
    simpa using h j b hb

/-- Odd supercentral elements anticommute with odd homogeneous elements. -/
theorem IsSupercentral.odd_anticomm {a : A} (h : IsSupercentral 𝒜 1 a)
    {b : A} (hb : b ∈ 𝒜 1) : a * b = -(b * a) := by
  have := h 1 b hb
  simpa using this

end Superfusion
