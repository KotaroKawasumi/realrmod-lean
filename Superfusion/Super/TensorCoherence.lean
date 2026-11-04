import Superfusion.Super.TensorGradingUnitor

/-!
# Bundled coherence for graded tensor products

This file packages the functoriality, associator, and Koszul braiding of
the graded tensor product as equivalences of bundled superalgebras.
These maps belong to the tensor structure itself: they do not depend on
matrix stabilization, Brauer--Wall classes, finite-dimensionality, or a
choice of basis.

Keeping them in this lightweight file lets abstract module and
bimodule constructions use tensor coherence without importing the
Brauer--Wall classification machinery.
-/

set_option autoImplicit false

universe u v₀ v₁ v₂ v₃ v₄ v₅

namespace Superfusion

open GradedTensorProduct
open scoped TensorProduct

variable {K : Type u} [CommRing K]

namespace SuperAlgEquiv

variable {P : SuperAlgebra.{u, v₀} K}
variable {P' : SuperAlgebra.{u, v₁} K}
variable {Q : SuperAlgebra.{u, v₂} K}
variable {Q' : SuperAlgebra.{u, v₃} K}

/-- The graded tensor product of two bundled superalgebra
equivalences. -/
noncomputable def gtensorCongr
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q') :
    SuperAlgEquiv (P.gtensor Q) (P'.gtensor Q') :=
  ⟨gcongr P.grading Q.grading P'.grading Q'.grading
      e.toAlgEquiv f.toAlgEquiv e.map_grading f.map_grading,
    gcongr_map_grading P.grading Q.grading P'.grading Q'.grading
      e.toAlgEquiv f.toAlgEquiv e.map_grading f.map_grading⟩

/-- The bundled tensor congruence acts factorwise on pure tensors. -/
theorem gtensorCongr_tmul
    (e : SuperAlgEquiv P P') (f : SuperAlgEquiv Q Q')
    (x : P.carrier) (y : Q.carrier) :
    (e.gtensorCongr f).toAlgEquiv
        (show P.grading ᵍ⊗[K] Q.grading from x ᵍ⊗ₜ[K] y) =
      (show P'.grading ᵍ⊗[K] Q'.grading from
        e.toAlgEquiv x ᵍ⊗ₜ[K] f.toAlgEquiv y) :=
  gcongr_tmul P.grading Q.grading P'.grading Q'.grading
    e.toAlgEquiv f.toAlgEquiv e.map_grading f.map_grading x y

end SuperAlgEquiv

variable (P : SuperAlgebra.{u, v₀} K)
variable (Q : SuperAlgebra.{u, v₁} K)
variable (R : SuperAlgebra.{u, v₂} K)

/-- The unit of a bundled graded tensor product is the pure tensor of
the two coefficient units. -/
theorem gtensor_one_one :
    (show P.grading ᵍ⊗[K] Q.grading from
      (1 : P.carrier) ᵍ⊗ₜ[K] (1 : Q.carrier)) =
      (1 : (P.gtensor Q).carrier) := by
  show GradedTensorProduct.of K P.grading Q.grading
      ((1 : P.carrier) ⊗ₜ[K] (1 : Q.carrier)) = 1
  rw [← Algebra.TensorProduct.one_def, GradedTensorProduct.of_one]

/-- The bundled associator of the graded tensor product. -/
noncomputable def gtensorAssoc :
    SuperAlgEquiv ((P.gtensor Q).gtensor R) (P.gtensor (Q.gtensor R)) :=
  ⟨gassoc P.grading Q.grading R.grading,
    gassoc_map_grading P.grading Q.grading R.grading⟩

/-- The bundled associator introduces no sign on pure tensors. -/
theorem gtensorAssoc_tmul
    (x : P.carrier) (y : Q.carrier) (z : R.carrier) :
    (gtensorAssoc P Q R).toAlgEquiv
        (show
            tensorGrading P.grading Q.grading ᵍ⊗[K] R.grading
          from
            (show P.grading ᵍ⊗[K] Q.grading from
                x ᵍ⊗ₜ[K] y) ᵍ⊗ₜ[K] z) =
      (show
          P.grading ᵍ⊗[K] tensorGrading Q.grading R.grading
        from
          x ᵍ⊗ₜ[K]
            (show Q.grading ᵍ⊗[K] R.grading from
              y ᵍ⊗ₜ[K] z)) :=
  gassoc_tmul P.grading Q.grading R.grading x y z

/-- The bundled Koszul braiding of the graded tensor product. -/
noncomputable def gtensorComm :
    SuperAlgEquiv (P.gtensor Q) (Q.gtensor P) :=
  ⟨comm P.grading Q.grading,
    comm_map_grading P.grading Q.grading⟩

/-- On homogeneous pure tensors, the bundled braiding contributes the
Koszul sign. -/
theorem gtensorComm_tmul_of_mem
    {i j : ZMod 2}
    {x : P.carrier} (hx : x ∈ P.grading i)
    {y : Q.carrier} (hy : y ∈ Q.grading j) :
    (gtensorComm P Q).toAlgEquiv
        (show P.grading ᵍ⊗[K] Q.grading from x ᵍ⊗ₜ[K] y) =
      (-1 : ℤˣ) ^ (j * i) •
        (show Q.grading ᵍ⊗[K] P.grading from y ᵍ⊗ₜ[K] x) := by
  exact comm_coe_tmul_coe P.grading Q.grading
    (⟨x, hx⟩ : P.grading i) (⟨y, hy⟩ : Q.grading j)

end Superfusion
