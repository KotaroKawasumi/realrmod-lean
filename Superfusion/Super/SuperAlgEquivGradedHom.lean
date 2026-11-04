import Mathlib.RingTheory.GradedAlgebra.AlgHom
import Superfusion.Super.BWPeriodicity

/-!
# Graded algebra homomorphisms underlying superalgebra equivalences

A bundled `SuperAlgEquiv` preserves every homogeneous component by
definition.  This file records the corresponding elementwise API and
forgets bijectivity to obtain mathlib's `GradedAlgHom`.

Keeping this bridge next to `SuperAlgEquiv`, rather than inside a
particular module construction, lets coefficient restriction and
gauge-index transport share the same lightweight interface.
-/

set_option autoImplicit false

universe u v₀ v₁ vI vA

namespace Superfusion.SuperAlgEquiv

variable {K : Type u} [CommRing K]
variable {P : SuperAlgebra.{u, v₀} K}
variable {Q : SuperAlgebra.{u, v₁} K}

/-- A bundled graded algebra equivalence maps each homogeneous component
into the component of the same degree. -/
theorem map_mem_grading
    (e : SuperAlgEquiv P Q)
    {i : ZMod 2} {x : P.carrier} (hx : x ∈ P.grading i) :
    e.toAlgEquiv x ∈ Q.grading i := by
  rw [← e.map_grading i]
  exact ⟨x, hx, rfl⟩

/-- Component membership is preserved and reflected by a bundled graded
algebra equivalence. -/
@[simp]
theorem map_mem_grading_iff
    (e : SuperAlgEquiv P Q)
    {i : ZMod 2} {x : P.carrier} :
    e.toAlgEquiv x ∈ Q.grading i ↔ x ∈ P.grading i := by
  constructor
  · intro hx
    have h := e.symm.map_mem_grading hx
    change e.toAlgEquiv.symm (e.toAlgEquiv x) ∈ P.grading i at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact e.map_mem_grading

/-- Forget bijectivity while retaining algebraic and grading
compatibility. -/
def toGradedAlgHom (e : SuperAlgEquiv P Q) :
    P.grading →ₐᵍ[K] Q.grading where
  toAlgHom := e.toAlgEquiv.toAlgHom
  map_mem := e.map_mem_grading

@[simp]
theorem toGradedAlgHom_apply
    (e : SuperAlgEquiv P Q) (x : P.carrier) :
    e.toGradedAlgHom x = e.toAlgEquiv x :=
  rfl

end Superfusion.SuperAlgEquiv

namespace Superfusion

variable {K : Type u} [CommRing K]
variable {I : Type vI}

/-- Equality transport in an arbitrary family of bundled
superalgebras.

This construction uses no algebraic structure on the index type.  It
is the coefficient-frame cast needed when two syntactically different
indices are propositionally equal. -/
def superAlgebraFamilyCast
    (D : I → SuperAlgebra.{u, vA} K)
    {i j : I} (h : i = j) :
    SuperAlgEquiv (D i) (D j) := by
  subst h
  exact SuperAlgEquiv.refl _

/-- Transport along reflexivity is the identity equivalence. -/
@[simp]
theorem superAlgebraFamilyCast_refl
    (D : I → SuperAlgebra.{u, vA} K) (i : I) :
    superAlgebraFamilyCast D (rfl : i = i) =
      SuperAlgEquiv.refl (D i) :=
  rfl

/-- Equality transports compose according to equality
transitivity. -/
@[simp]
theorem superAlgebraFamilyCast_trans
    (D : I → SuperAlgebra.{u, vA} K)
    {i j k : I} (h₁ : i = j) (h₂ : j = k) :
    (superAlgebraFamilyCast D h₁).trans
        (superAlgebraFamilyCast D h₂) =
      superAlgebraFamilyCast D (h₁.trans h₂) := by
  subst h₁
  subst h₂
  rfl

/-- Inverting equality transport corresponds to symmetry of the
index equality. -/
@[simp]
theorem superAlgebraFamilyCast_symm
    (D : I → SuperAlgebra.{u, vA} K)
    {i j : I} (h : i = j) :
    (superAlgebraFamilyCast D h).symm =
      superAlgebraFamilyCast D h.symm := by
  subst h
  rfl

/-- Reflexive family transport acts identically on coefficients. -/
theorem superAlgebraFamilyCast_refl_apply
    (D : I → SuperAlgebra.{u, vA} K)
    (i : I) (x : (D i).carrier) :
    (superAlgebraFamilyCast D (rfl : i = i)).toAlgEquiv x = x :=
  rfl

/-- Coefficientwise form of composition of family transports. -/
@[simp]
theorem superAlgebraFamilyCast_trans_apply
    (D : I → SuperAlgebra.{u, vA} K)
    {i j k : I} (h₁ : i = j) (h₂ : j = k)
    (x : (D i).carrier) :
    (superAlgebraFamilyCast D h₂).toAlgEquiv
        ((superAlgebraFamilyCast D h₁).toAlgEquiv x) =
      (superAlgebraFamilyCast D (h₁.trans h₂)).toAlgEquiv x := by
  subst h₁
  subst h₂
  rfl

/-- Coefficientwise form of symmetry of family transport. -/
@[simp]
theorem superAlgebraFamilyCast_symm_apply
    (D : I → SuperAlgebra.{u, vA} K)
    {i j : I} (h : i = j) (x : (D j).carrier) :
    (superAlgebraFamilyCast D h).toAlgEquiv.symm x =
      (superAlgebraFamilyCast D h.symm).toAlgEquiv x := by
  subst h
  rfl

/-- Equality transport in a superalgebra family preserves
homogeneous degree. -/
theorem superAlgebraFamilyCast_mem_grading
    (D : I → SuperAlgebra.{u, vA} K)
    {i j : I} (h : i = j)
    {d : ZMod 2} {x : (D i).carrier}
    (hx : x ∈ (D i).grading d) :
    (superAlgebraFamilyCast D h).toAlgEquiv x ∈
      (D j).grading d :=
  (superAlgebraFamilyCast D h).map_mem_grading hx

end Superfusion
