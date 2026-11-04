/-
Superfusion / Super / TowerLift

Milestone M7d-3a: **mapping the division tower into a target algebra**.

Given elements `γ 0, …, γ (N-1)` of a `K`-algebra `C`, pairwise
anticommuting and each squaring to `ε`, the universal property of the
odd double (M7d-2) iterates to an algebra map

  `towerLift : (divisionTower ε n).carrier →ₐ[K] C`   (`n ≤ N`)

sending the `k`-th adjoined generator to `γ k`.  The recursion carries
the invariant (`GammaConj`) that every *later* `γ m` (with `m < N`)
supercommutes with the image — that is exactly the conjugation
hypothesis the next `lift` needs.  If `C` is graded and the `γ i` are
odd, the map is grade-preserving (`towerLift_isHomogeneous`), and out
of a graded-simple floor it is automatically injective
(`towerLift_injective`).

This is the workhorse of the Bott certificate (M7d-3b): eight explicit
anticommuting odd matrices in `M_{8|8}(ℝ)` give an injective graded map
from `D₁^{⊗̂8}`, surjective by the dimension count `2⁸ = 16²`.
-/
import Superfusion.Super.OddDoubleLift
import Superfusion.Super.GradedTransfer
import Superfusion.Super.DivisionTower

namespace Superfusion

section Bridge

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
variable {C : Type*} [Ring C] [Algebra K C]

/-- Supercommutation with homogeneous images upgrades to the
`J`-conjugation rule needed by `OddDouble.lift`. -/
theorem conj_of_supercommutes (g : A →ₐ[K] C) (c : C)
    (h : ∀ (i : ZMod 2), ∀ a ∈ 𝒜 i,
      c * g a = ((sgn i : ℤˣ) : ℤ) • (g a * c))
    (a : A) : c * g a = g (parityMap 𝒜 a) * c := by
  have hsplit : a = evenPart 𝒜 a + oddPart 𝒜 a :=
    (evenPart_add_oddPart 𝒜 a).symm
  conv_lhs => rw [hsplit]
  rw [map_add, mul_add, h 0 _ (evenPart_mem 𝒜 a), h 1 _ (oddPart_mem 𝒜 a),
    parityMap_apply, map_sub, sub_mul]
  simp only [sgn_zero, sgn_one, units_sign_eq, Units.val_one,
    Units.val_neg, one_smul, neg_smul]
  abel

end Bridge

section Tower

variable {K : Type*} [CommRing K]
variable {C : Type*} [Ring C] [Algebra K C]
variable (ε : K) (γ : ℕ → C) (N : ℕ)

/-- The recursion invariant, stated over an arbitrary superalgebra:
every `γ m` with `n ≤ m < N` supercommutes with the image of `f`. -/
def GammaConj (n : ℕ) {A : Type*} [Ring A] [Algebra K A]
    (𝒜 : ZMod 2 → Submodule K A) (f : A →ₐ[K] C) : Prop :=
  ∀ m, n ≤ m → m < N → ∀ (i : ZMod 2), ∀ a ∈ 𝒜 i,
    γ m * f a = ((sgn i : ℤˣ) : ℤ) • (f a * γ m)

private theorem sgn_succ_cast (i : ZMod 2) :
    ((sgn (i + 1) : ℤˣ) : ℤ) = -((sgn i : ℤˣ) : ℤ) := by
  rcases zmod2_cases i with hi | hi <;> subst hi <;>
    simp [show ((1 : ZMod 2) + 1) = 0 by decide]

variable (hsq : ∀ i, i < N → γ i * γ i = algebraMap K C ε)
variable (hanti : ∀ i j : ℕ, i < N → j < N → i ≠ j →
  γ i * γ j = -(γ j * γ i))

include hanti in
/-- The invariant propagates through one odd-double lift. -/
private theorem gammaConj_lift {n : ℕ} (hnN : n < N) {A : Type*} [Ring A]
    [Algebra K A] {𝒜 : ZMod 2 → Submodule K A} [GradedAlgebra 𝒜]
    {f : A →ₐ[K] C} (hf : GammaConj γ N n 𝒜 f)
    (hc : ∀ a, γ n * f a = f (parityMap 𝒜 a) * γ n)
    (hsqn : γ n * γ n = algebraMap K C ε) :
    GammaConj γ N (n + 1) (OddDouble.grading 𝒜 ε)
      (OddDouble.lift 𝒜 ε f (γ n) hsqn hc) := by
  intro m hm hmN i x hx
  have hle : n ≤ m := Nat.le_of_succ_le hm
  have hmn : m ≠ n := by omega
  obtain ⟨h1, h2⟩ := (OddDouble.mem_grading 𝒜 ε).mp hx
  conv_lhs => rw [← OddDouble.mk_p1_p2 𝒜 ε x, OddDouble.lift_mk]
  conv_rhs => rw [← OddDouble.mk_p1_p2 𝒜 ε x, OddDouble.lift_mk]
  have hterm2 : γ m * (f (OddDouble.p2 𝒜 ε x) * γ n)
      = ((sgn i : ℤˣ) : ℤ)
        • (f (OddDouble.p2 𝒜 ε x) * γ n * γ m) := by
    rw [← mul_assoc, hf m hle hmN (i + 1) _ h2, smul_mul_assoc, mul_assoc,
      hanti m n hmN hnN hmn, mul_neg, smul_neg, sgn_succ_cast, neg_smul,
      neg_neg, ← mul_assoc]
  rw [mul_add, hterm2, hf m hle hmN i _ h1, add_mul, smul_add]

/-- The iterated lift, bundled with its invariant. -/
noncomputable def towerLiftAux :
    (n : ℕ) → n ≤ N →
      {f : (divisionTower ε n).carrier →ₐ[K] C //
        GammaConj γ N n (divisionTower ε n).grading f}
  | 0, _ =>
    ⟨Algebra.ofId K C, by
      intro m _ _ i a ha
      rcases zmod2_cases i with hi | hi <;> subst hi
      · rw [sgn_zero]
        simp only [Units.val_one, one_smul]
        show γ m * algebraMap K C a = algebraMap K C a * γ m
        exact (Algebra.commutes (R := K) a (γ m)).symm
      · have ha0 : a = 0 := (Submodule.mem_bot K).mp ha
        rw [ha0, map_zero, mul_zero, zero_mul, smul_zero]⟩
  | n + 1, hn =>
    have hn' : n ≤ N := Nat.le_of_succ_le hn
    have hnN : n < N := hn
    ⟨OddDouble.lift (divisionTower ε n).grading ε
        (towerLiftAux n hn').1 (γ n) (hsq n hnN)
        (conj_of_supercommutes (divisionTower ε n).grading
          (towerLiftAux n hn').1 (γ n)
          (fun i a ha => (towerLiftAux n hn').2 n le_rfl hnN i a ha)),
     gammaConj_lift ε γ N hanti hnN (towerLiftAux n hn').2 _ _⟩

/-- The iterated lift `divisionTower ε n → C`, sending the `k`-th
adjoined odd generator to `γ k`. -/
noncomputable def towerLift (n : ℕ) (hn : n ≤ N) :
    (divisionTower ε n).carrier →ₐ[K] C :=
  (towerLiftAux ε γ N hsq hanti n hn).1

/-- The invariant, exported: later `γ`'s supercommute with the image. -/
theorem towerLift_conj (n : ℕ) (hn : n ≤ N) :
    GammaConj γ N n (divisionTower ε n).grading
      (towerLift ε γ N hsq hanti n hn) :=
  (towerLiftAux ε γ N hsq hanti n hn).2

@[simp] theorem towerLift_zero (h0 : 0 ≤ N) (a : K) :
    towerLift ε γ N hsq hanti 0 h0 a = algebraMap K C a := rfl

theorem towerLift_succ_mk (n : ℕ) (hn : n + 1 ≤ N)
    (a b : (divisionTower ε n).carrier) :
    towerLift ε γ N hsq hanti (n + 1) hn
        (OddDouble.mk (divisionTower ε n).grading ε a b)
      = towerLift ε γ N hsq hanti n (Nat.le_of_succ_le hn) a
        + towerLift ε γ N hsq hanti n (Nat.le_of_succ_le hn) b * γ n :=
  OddDouble.lift_mk (divisionTower ε n).grading ε
    (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
    (hsq n hn)
    (conj_of_supercommutes (divisionTower ε n).grading
      (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
      (fun i a ha =>
        (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).2
          n le_rfl hn i a ha)) a b

@[simp] theorem towerLift_gen (n : ℕ) (hn : n + 1 ≤ N) :
    towerLift ε γ N hsq hanti (n + 1) hn
        (OddDouble.gen (divisionTower ε n).grading ε) = γ n :=
  OddDouble.lift_gen (divisionTower ε n).grading ε
    (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
    (hsq n hn)
    (conj_of_supercommutes (divisionTower ε n).grading
      (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
      (fun i a ha =>
        (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).2
          n le_rfl hn i a ha))

/-- If the target is graded and the `γ i` are odd, the iterated lift is
grade-preserving. -/
theorem towerLift_isHomogeneous (ℭ : ZMod 2 → Submodule K C)
    [GradedAlgebra ℭ] (hodd : ∀ i, γ i ∈ ℭ 1) :
    ∀ (n : ℕ) (hn : n ≤ N),
      IsHomogeneousHom (divisionTower ε n).grading ℭ
        (towerLift ε γ N hsq hanti n hn)
  | 0, _ => by
      intro i a ha
      rcases zmod2_cases i with hi | hi <;> subst hi
      · exact algebraMap_mem_grade_zero ℭ a
      · have ha0 : a = 0 := (Submodule.mem_bot K).mp ha
        rw [ha0, map_zero]
        exact zero_mem _
  | n + 1, hn => by
      have IH := towerLift_isHomogeneous ℭ hodd n (Nat.le_of_succ_le hn)
      exact OddDouble.lift_isHomogeneous (divisionTower ε n).grading ε
        (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
        (hsq n hn)
        (conj_of_supercommutes (divisionTower ε n).grading
          (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).1 (γ n)
          (fun i a ha =>
            (towerLiftAux ε γ N hsq hanti n (Nat.le_of_succ_le hn)).2
              n le_rfl hn i a ha))
        ℭ IH (hodd n)

end Tower

section Injective

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {C : Type*} [Ring C] [Algebra K C] [Nontrivial C]
variable {ε : K} (γ : ℕ → C) (N : ℕ)
variable (hsq : ∀ i, i < N → γ i * γ i = algebraMap K C ε)
variable (hanti : ∀ i j : ℕ, i < N → j < N → i ≠ j →
  γ i * γ j = -(γ j * γ i))

/-- Out of a graded-simple floor of the tower, a graded iterated lift is
automatically injective — half of the Bott certificate. -/
theorem towerLift_injective (hε : ε ≠ 0) (ℭ : ZMod 2 → Submodule K C)
    [GradedAlgebra ℭ] (hodd : ∀ i, γ i ∈ ℭ 1) (n : ℕ) (hn : n ≤ N) :
    Function.Injective (towerLift ε γ N hsq hanti n hn) := by
  haveI := divisionTower_isGradedSimple (K := K) hε n
  exact injective_of_isGradedSimple (divisionTower ε n).grading ℭ
    (towerLift ε γ N hsq hanti n hn)
    (towerLift_isHomogeneous ε γ N hsq hanti ℭ hodd n hn)

end Injective

end Superfusion
