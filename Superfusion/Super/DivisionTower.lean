/-
Superfusion / Super / DivisionTower

Milestone M7c-2: the standard super division algebras, as iterated odd
doubles.

`divisionTower ε n` is the `n`-fold odd double (M7c-1) of the base
field `K` with its purely even grading — the explicit model of
`D_ε^{⊗̂ n}`, i.e. the Clifford algebra of the diagonal form
`ε(x₁² + ⋯ + x_n²)`.  Over `ℝ`, `DReal n` (`n : ℤ`, the sign of `n`
choosing `ε = ±1`) are the standard super division algebras `D_n` of
the paper (§2.2, §4).

Main results (field base, `2` invertible, `ε ≠ 0`):

* every floor of the tower is a central simple superalgebra
  (`divisionTower_isSuperCentral`, `divisionTower_isGradedSimple`),
  hence super-Azumaya (`divisionTower_isSuperAzumaya`);
* `finrank K (divisionTower ε n) = 2^n` (`divisionTower_finrank`);
* the corollaries for `DReal` over `ℝ`.

**Indexing note.**  The tower is indexed by `ℕ` (and `DReal` by `ℤ`);
`ℤ/8` appears nowhere.  That these algebras represent the classes of
the Brauer–Wall group `BW(ℝ) ≅ ℤ/8` — in particular that the index
matters only mod `8` up to BW-equivalence (`D₁^{⊗̂ 8} ∼ M₁₆(ℝ)`) — is
a *Morita* statement requiring matrix superalgebras and the BW group
itself, and is deliberately not part of this milestone.
-/
import Superfusion.Super.OddDouble
import Superfusion.Super.EvenGrading
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Data.Real.Basic

namespace Superfusion

/-- A bundled superalgebra over `K`. -/
structure SuperAlgebra (K : Type*) [CommRing K] where
  /-- The underlying type. -/
  carrier : Type*
  [ring : Ring carrier]
  [algebra : Algebra K carrier]
  /-- The `ZMod 2`-grading. -/
  grading : ZMod 2 → Submodule K carrier
  [gradedAlgebra : GradedAlgebra grading]

attribute [instance] SuperAlgebra.ring SuperAlgebra.algebra
  SuperAlgebra.gradedAlgebra

namespace SuperAlgebra

variable (K : Type*) [CommRing K]

/-- The base field, purely even. -/
def base : SuperAlgebra K where
  carrier := K
  grading := evenGrading K K

variable {K}

/-- The odd double, at the bundled level. -/
noncomputable def oddDouble (P : SuperAlgebra K) (ε : K) : SuperAlgebra K where
  carrier := OddDouble P.grading ε
  grading := OddDouble.grading P.grading ε

end SuperAlgebra

variable {K : Type*} [CommRing K]

/-- The division tower: the `n`-fold odd double of the purely even base
field, the explicit model of `D_ε^{⊗̂ n}` (the Clifford algebra of
`ε(x₁² + ⋯ + x_n²)`). -/
noncomputable def divisionTower (ε : K) : ℕ → SuperAlgebra K
  | 0 => .base K
  | n + 1 => (divisionTower ε n).oddDouble ε

@[simp] theorem divisionTower_zero (ε : K) :
    divisionTower ε 0 = .base K := rfl

@[simp] theorem divisionTower_succ (ε : K) (n : ℕ) :
    divisionTower ε (n + 1) = (divisionTower ε n).oddDouble ε := rfl

theorem divisionTower_finite (ε : K) :
    ∀ n, Module.Finite K (divisionTower ε n).carrier
  | 0 => inferInstanceAs (Module.Finite K K)
  | n + 1 => by
      haveI := divisionTower_finite ε n
      exact inferInstanceAs
        (Module.Finite K (OddDouble (divisionTower ε n).grading ε))

theorem divisionTower_nontrivial (ε : K) [Nontrivial K] :
    ∀ n, Nontrivial (divisionTower ε n).carrier
  | 0 => inferInstanceAs (Nontrivial K)
  | n + 1 => by
      haveI := divisionTower_nontrivial ε n
      exact inferInstanceAs
        (Nontrivial (OddDouble (divisionTower ε n).grading ε))

/-! ### Central simplicity, floor by floor -/

section Field

variable {K : Type*} [Field K]

/-- The purely even base field is supercentral. -/
theorem base_isSuperCentral : IsSuperCentral (SuperAlgebra.base K).grading :=
  ⟨fun x _ => Submodule.mem_one.mpr ⟨x, rfl⟩⟩

/-- The purely even base field is graded-simple. -/
theorem base_isGradedSimple : IsGradedSimple (SuperAlgebra.base K).grading := by
  haveI : IsSimpleRing (SuperAlgebra.base K).carrier :=
    inferInstanceAs (IsSimpleRing K)
  exact isGradedSimple_of_isSimpleRing _

theorem divisionTower_isSuperCentral [Invertible (2 : K)] {ε : K}
    (hε : ε ≠ 0) : ∀ n, IsSuperCentral (divisionTower ε n).grading
  | 0 => base_isSuperCentral
  | n + 1 => by
      haveI := divisionTower_isSuperCentral hε n
      exact OddDouble.isSuperCentral (divisionTower ε n).grading ε hε

theorem divisionTower_isGradedSimple [Invertible (2 : K)] {ε : K}
    (hε : ε ≠ 0) : ∀ n, IsGradedSimple (divisionTower ε n).grading
  | 0 => base_isGradedSimple
  | n + 1 => by
      haveI := divisionTower_isGradedSimple hε n
      exact OddDouble.isGradedSimple (divisionTower ε n).grading ε hε

/-- **The standard super division algebras are super-Azumaya** (M7c-2):
every floor of the division tower is a central simple superalgebra, and
Wall's criterion holds. -/
theorem divisionTower_isSuperAzumaya [Invertible (2 : K)] {ε : K}
    (hε : ε ≠ 0) (n : ℕ) : IsSuperAzumaya (divisionTower ε n).grading := by
  haveI := divisionTower_isSuperCentral hε n
  haveI := divisionTower_isGradedSimple hε n
  haveI := divisionTower_finite ε n
  haveI := divisionTower_nontrivial ε n
  exact isSuperAzumaya_of_central_simple _

/-- The tower has the size of the Clifford algebras: `2^n`. -/
theorem divisionTower_finrank (ε : K) :
    ∀ n, Module.finrank K (divisionTower ε n).carrier = 2 ^ n
  | 0 => by
      rw [pow_zero]
      exact Module.finrank_self K
  | n + 1 => by
      haveI := divisionTower_finite ε n
      rw [divisionTower_succ]
      show Module.finrank K (OddDouble (divisionTower ε n).grading ε) = _
      rw [← (OddDouble.ofPair (divisionTower ε n).grading ε).finrank_eq,
        Module.finrank_prod, divisionTower_finrank ε n, pow_succ]
      ring

end Field

/-! ### The paper's `D_n` over `ℝ` -/

/-- The standard super division algebras over `ℝ`: `D_n = D_{±1}^{⊗̂ |n|}`
with the sign of `n : ℤ` choosing `ε = ±1` (§2.2).  That `D_n` only
depends on `n` mod `8` up to Brauer–Wall equivalence is a separate,
not-yet-formalized Morita statement. -/
noncomputable def DReal (n : ℤ) : SuperAlgebra ℝ :=
  divisionTower (if 0 ≤ n then (1 : ℝ) else -1) n.natAbs

/-- The standard super division algebras `D_n` over `ℝ` are central
simple superalgebras, hence super-Azumaya. -/
theorem DReal_isSuperAzumaya (n : ℤ) :
    IsSuperAzumaya (DReal n).grading := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  refine divisionTower_isSuperAzumaya ?_ _
  split_ifs
  · exact one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero

theorem DReal_finrank (n : ℤ) :
    Module.finrank ℝ (DReal n).carrier = 2 ^ n.natAbs :=
  divisionTower_finrank _ _

end Superfusion
