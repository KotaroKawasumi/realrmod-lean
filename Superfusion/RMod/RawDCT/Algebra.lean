import Mathlib.Data.ZMod.Basic

/-!
# Abstract data--laws separated graded algebras

This file contains only the general structures.  Concrete coordinate data
and proofs belong to instance-construction files.
-/

set_option autoImplicit false

universe u v

namespace Superfusion.RMod.RawDCT

/-- Computational contents of a `ZMod 2`-graded algebra. -/
structure SuperAlgebraData (K : Type u) where
  carrier : Type v
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  one : carrier
  mul : carrier → carrier → carrier
  smul : K → carrier → carrier
  component : ZMod 2 → carrier → carrier

namespace SuperAlgebraData

/-- Homogeneity derived from the stored executable projection. -/
def MemGrade {K : Type u} (d : SuperAlgebraData K) (i : ZMod 2)
    (x : d.carrier) : Prop :=
  d.component i x = x

end SuperAlgebraData

/-- Algebra, scalar, and grading laws for one concrete data record. -/
structure SuperAlgebraLaws {K : Type u} [CommRing K]
    (d : SuperAlgebraData K) : Prop where
  add_assoc : ∀ x y z, d.add (d.add x y) z = d.add x (d.add y z)
  add_comm : ∀ x y, d.add x y = d.add y x
  zero_add : ∀ x, d.add d.zero x = x
  add_zero : ∀ x, d.add x d.zero = x
  neg_add : ∀ x, d.add (d.neg x) x = d.zero
  add_neg : ∀ x, d.add x (d.neg x) = d.zero
  mul_assoc : ∀ x y z, d.mul (d.mul x y) z = d.mul x (d.mul y z)
  one_mul : ∀ x, d.mul d.one x = x
  mul_one : ∀ x, d.mul x d.one = x
  mul_add : ∀ x y z, d.mul x (d.add y z) = d.add (d.mul x y) (d.mul x z)
  add_mul : ∀ x y z, d.mul (d.add x y) z = d.add (d.mul x z) (d.mul y z)
  one_smul : ∀ x, d.smul 1 x = x
  smul_assoc : ∀ r s x, d.smul (r * s) x = d.smul r (d.smul s x)
  add_smul : ∀ r s x, d.smul (r + s) x = d.add (d.smul r x) (d.smul s x)
  smul_add : ∀ r x y, d.smul r (d.add x y) = d.add (d.smul r x) (d.smul r y)
  zero_smul : ∀ x, d.smul 0 x = d.zero
  smul_zero : ∀ r, d.smul r d.zero = d.zero
  smul_mul : ∀ r x y, d.mul (d.smul r x) y = d.smul r (d.mul x y)
  mul_smul : ∀ r x y, d.mul x (d.smul r y) = d.smul r (d.mul x y)
  component_zero : ∀ i, d.component i d.zero = d.zero
  component_add : ∀ i x y,
    d.component i (d.add x y) = d.add (d.component i x) (d.component i y)
  component_neg : ∀ i x, d.component i (d.neg x) = d.neg (d.component i x)
  component_smul : ∀ i r x, d.component i (d.smul r x) = d.smul r (d.component i x)
  component_idem : ∀ i x, d.component i (d.component i x) = d.component i x
  component_complement : ∀ i x,
    d.add (d.component i x) (d.component (i + 1) x) = x
  grade_disjoint : ∀ i x,
    d.MemGrade i x → d.MemGrade (i + 1) x → x = d.zero
  one_mem : d.MemGrade 0 d.one
  mul_mem : ∀ i j x y,
    d.MemGrade i x → d.MemGrade j y → d.MemGrade (i + j) (d.mul x y)

/-- A completed constructive graded algebra. -/
structure ConstructiveSuperAlgebra (K : Type u) [CommRing K] where
  data : SuperAlgebraData.{u, v} K
  laws : SuperAlgebraLaws data

end Superfusion.RMod.RawDCT
