/-
Superfusion / Super / BWGroup

Milestone M7f-4d: **the Brauer–Wall monoid and group**.  Classes of
nontrivial finite-dimensional superalgebras over a field under
Brauer–Wall equivalence, with the graded tensor product:

- well-definedness on classes is M7f-4b (matrix stabilization
  commutes with `ᵍ⊗`, both factors),
- associativity is M7f-1c (`gassoc`), the unit laws are M7f-4a
  (unitors), commutativity is the Koszul braiding (M7f-1g),
- and the super-Azumaya classes are **units**: `[P]⁻¹ = [P^sop]`,
  by Wall's isomorphism and M7f-4c (`[P]·[P^sop] = [End P] = 1`).

The Brauer–Wall group `BW K` is the unit group of the class monoid.
-/
import Superfusion.Super.MatrixSuperTensor
import Superfusion.Super.TensorCoherence
import Superfusion.Super.GradedEndMatrix

namespace Superfusion

open Module
open TensorProduct
open GradedTensorProduct

/-! ### Bundled congruences of the graded tensor product -/

section Congr

variable {K : Type*} [CommRing K]

/-! ### The Brauer–Wall product is well defined on classes -/

/-- Tensoring on the right preserves Brauer–Wall equivalence
(M7f-4b). -/
theorem IsBWEquivalent.gtensor_right {P P' : SuperAlgebra K}
    (h : IsBWEquivalent P P') (Q : SuperAlgebra K) :
    IsBWEquivalent (P.gtensor Q) (P'.gtensor Q) := by
  obtain ⟨p, q, r, s, hpq, hrs, ⟨e⟩⟩ := h
  exact ⟨p, q, r, s, hpq, hrs,
    ⟨((matrixSuperGtensor P Q p q).symm).trans
      ((e.gtensorCongr (SuperAlgEquiv.refl Q)).trans
        (matrixSuperGtensor P' Q r s))⟩⟩

/-- Tensoring on the left preserves Brauer–Wall equivalence
(M7f-4b, right-factor version via the braiding). -/
theorem IsBWEquivalent.gtensor_left {Q Q' : SuperAlgebra K}
    (h : IsBWEquivalent Q Q') (P : SuperAlgebra K) :
    IsBWEquivalent (P.gtensor Q) (P.gtensor Q') := by
  obtain ⟨p, q, r, s, hpq, hrs, ⟨e⟩⟩ := h
  exact ⟨p, q, r, s, hpq, hrs,
    ⟨((matrixSuperGtensorRight P Q p q).symm).trans
      (((SuperAlgEquiv.refl P).gtensorCongr e).trans
        (matrixSuperGtensorRight P Q' r s))⟩⟩

/-- **The Brauer–Wall product is well defined** (M7f-4d): the graded
tensor product descends to BW classes. -/
theorem IsBWEquivalent.gtensor_congr {P P' Q Q' : SuperAlgebra K}
    (hP : IsBWEquivalent P P') (hQ : IsBWEquivalent Q Q') :
    IsBWEquivalent (P.gtensor Q) (P'.gtensor Q') :=
  (hP.gtensor_right Q).trans (hQ.gtensor_left P')

end Congr

/-! ### Closure of the class carrier -/

section Closure

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]

theorem finite_gtensor (𝒜 : ZMod 2 → Submodule K A)
    (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [Module.Finite K A] [Module.Finite K B] :
    Module.Finite K (𝒜 ᵍ⊗[K] ℬ) :=
  Module.Finite.equiv (GradedTensorProduct.of K 𝒜 ℬ)

theorem nontrivial_gtensor (𝒜 : ZMod 2 → Submodule K A)
    (ℬ : ZMod 2 → Submodule K B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    [FiniteDimensional K A] [FiniteDimensional K B]
    [Nontrivial A] [Nontrivial B] :
    Nontrivial (𝒜 ᵍ⊗[K] ℬ) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [← (GradedTensorProduct.of K 𝒜 ℬ).finrank_eq,
    Module.finrank_tensorProduct]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

theorem finite_sop (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
    [Module.Finite K A] :
    Module.Finite K (SuperOp 𝒜) :=
  Module.Finite.equiv (SuperOp.op 𝒜)

theorem nontrivial_sop (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
    [Nontrivial A] :
    Nontrivial (SuperOp 𝒜) :=
  (SuperOp.op 𝒜).toEquiv.symm.nontrivial

end Closure

section CarrierInstances

variable {K : Type*} [Field K]

instance (P Q : SuperAlgebra K) [FiniteDimensional K P.carrier]
    [FiniteDimensional K Q.carrier] :
    FiniteDimensional K (P.gtensor Q).carrier :=
  finite_gtensor P.grading Q.grading

instance (P Q : SuperAlgebra K) [FiniteDimensional K P.carrier]
    [FiniteDimensional K Q.carrier] [Nontrivial P.carrier]
    [Nontrivial Q.carrier] :
    Nontrivial (P.gtensor Q).carrier :=
  nontrivial_gtensor P.grading Q.grading

instance (P : SuperAlgebra K) [FiniteDimensional K P.carrier] :
    FiniteDimensional K P.sop.carrier :=
  finite_sop P.grading

instance (P : SuperAlgebra K) [Nontrivial P.carrier] :
    Nontrivial P.sop.carrier :=
  nontrivial_sop P.grading

instance : FiniteDimensional K (SuperAlgebra.base K).carrier :=
  inferInstanceAs (FiniteDimensional K K)

instance : Nontrivial (SuperAlgebra.base K).carrier :=
  inferInstanceAs (Nontrivial K)

end CarrierInstances

/-! ### The Brauer–Wall class monoid -/

section Monoid

universe u

variable (K : Type u) [Field K]

/-- Representatives of Brauer–Wall classes: nontrivial
finite-dimensional bundled superalgebras.

The carrier universe is pinned to `u` (the universe of `K` itself):
`SuperAlgebra.base` forces this, since its carrier *is* `K`, so a
`One` for the class monoid is only available at this universe. -/
def BWRep :=
  {P : SuperAlgebra.{u, u} K //
    FiniteDimensional K P.carrier ∧ Nontrivial P.carrier}

/-- Brauer–Wall equivalence as a setoid on representatives. -/
def bwSetoid : Setoid (BWRep.{u} K) where
  r P Q := IsBWEquivalent P.1 Q.1
  iseqv := ⟨fun P => IsBWEquivalent.refl P.1,
    IsBWEquivalent.symm, IsBWEquivalent.trans⟩

/-- The Brauer–Wall class monoid of `K`. -/
def BWMonoid := Quotient (bwSetoid.{u} K)

variable {K}

/-- The Brauer–Wall class of a bundled superalgebra. -/
def BWMonoid.mk (P : SuperAlgebra.{u, u} K) [FiniteDimensional K P.carrier]
    [Nontrivial P.carrier] : BWMonoid.{u} K :=
  Quotient.mk (bwSetoid K) ⟨P, inferInstance, inferInstance⟩

theorem BWMonoid.mk_eq_mk_iff {P Q : SuperAlgebra.{u, u} K}
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [FiniteDimensional K Q.carrier] [Nontrivial Q.carrier] :
    BWMonoid.mk P = BWMonoid.mk Q ↔ IsBWEquivalent P Q :=
  ⟨fun h => Quotient.exact h,
    fun h => Quotient.sound (s := bwSetoid K) h⟩

namespace BWMonoid

noncomputable instance : Mul (BWMonoid.{u} K) :=
  ⟨Quotient.map₂ (fun P Q =>
      ⟨P.1.gtensor Q.1, by
        haveI := P.2.1; haveI := P.2.2
        haveI := Q.2.1; haveI := Q.2.2
        exact ⟨finite_gtensor P.1.grading Q.1.grading,
          nontrivial_gtensor P.1.grading Q.1.grading⟩⟩)
    (fun _ _ hP _ _ hQ => hP.gtensor_congr hQ)⟩

noncomputable instance : One (BWMonoid.{u} K) :=
  ⟨BWMonoid.mk (.base K)⟩

theorem mk_mul (P Q : SuperAlgebra.{u, u} K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [FiniteDimensional K Q.carrier] [Nontrivial Q.carrier] :
    BWMonoid.mk P * BWMonoid.mk Q = BWMonoid.mk (P.gtensor Q) := rfl

theorem one_def : (1 : BWMonoid.{u} K) = BWMonoid.mk (.base K) := rfl

/-- **The Brauer–Wall class monoid** (M7f-4d): associativity from
`gassoc`, unit laws from the unitors, commutativity from the Koszul
braiding. -/
noncomputable instance instCommMonoid : CommMonoid (BWMonoid.{u} K) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c :=
    Quotient.inductionOn₃ a b c fun P Q R =>
      Quotient.sound (IsBWEquivalent.of_superAlgEquiv
        (gtensorAssoc P.1 Q.1 R.1))
  one_mul a :=
    Quotient.inductionOn a fun P =>
      Quotient.sound (IsBWEquivalent.of_superAlgEquiv
        (gtensorUnitorLeft P.1))
  mul_one a :=
    Quotient.inductionOn a fun P =>
      Quotient.sound (IsBWEquivalent.of_superAlgEquiv
        (gtensorUnitorRight P.1))
  mul_comm a b :=
    Quotient.inductionOn₂ a b fun P Q =>
      Quotient.sound (IsBWEquivalent.of_superAlgEquiv
        (gtensorComm P.1 Q.1))

end BWMonoid

variable (K) in
/-- **The Brauer–Wall group** of `K`: the unit group of the class
monoid. -/
def BW := (BWMonoid.{u} K)ˣ

noncomputable instance : CommGroup (BW.{u} K) :=
  inferInstanceAs (CommGroup (BWMonoid.{u} K)ˣ)

/-- **Super-Azumaya classes are units** (M7f-4c/4d):
`[P]⁻¹ = [P^sop]`. -/
noncomputable def BW.ofAzumaya (P : SuperAlgebra.{u, u} K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [IsSuperAzumaya P.grading] : BW.{u} K where
  val := BWMonoid.mk P
  inv := BWMonoid.mk P.sop
  val_inv := by
    rw [BWMonoid.mk_mul]
    exact Quotient.sound (isBWEquivalent_gtensor_sop_base P)
  inv_val := by
    rw [BWMonoid.mk_mul]
    exact Quotient.sound
      ((IsBWEquivalent.of_superAlgEquiv (gtensorComm P.sop P)).trans
        (isBWEquivalent_gtensor_sop_base P))

@[simp] theorem BW.ofAzumaya_val (P : SuperAlgebra.{u, u} K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [IsSuperAzumaya P.grading] :
    (BW.ofAzumaya P).val = BWMonoid.mk P := rfl

@[simp] theorem BW.ofAzumaya_inv (P : SuperAlgebra.{u, u} K)
    [FiniteDimensional K P.carrier] [Nontrivial P.carrier]
    [IsSuperAzumaya P.grading] :
    (BW.ofAzumaya P)⁻¹.val = BWMonoid.mk P.sop := rfl

end Monoid

end Superfusion
