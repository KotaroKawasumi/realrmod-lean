import RMod.BrundanEllis.StackingTensorHom
import RMod.Classification.Instances.HomogeneousSumTensor
import RMod.Classification.Instances.HomogeneousHom
import RMod.Classification.Proofs.TensorEndDimension
import RMod.Classification.Proofs.ReferenceComponentSpan
import Mathlib.Tactic.Ring

/-! Homogeneous sum presentations reduce all Hom dimensions within two
reference components to the tensor-endomorphism formula for simple objects.
Together with corner injectivity this proves bijectivity of the actual map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Preadditive
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking.Raw
open RMod.Classification
attribute [local implicit_reducible] CategoryTheory.End
variable (C : RMod.WeaklyPointedSuperfusion.{0, 0})

/-- Coordinates on the source of a Hom space, using the given homogeneous sum. -/
def homFromEquiv {S X : LinearCategory C} {n : ℕ} (d : HomogeneousSum C.data S X n)
    (U : LinearCategory C) : (X ⟶ U) ≃ₗ[ℝ] (Fin n → (S ⟶ U)) where
  toFun f i := d.data.inclusion i ≫ f
  invFun f := ∑ i, d.data.projection i ≫ f i
  left_inv f := by simp only [← Category.assoc, ← sum_comp, d.total, Category.id_comp]
  right_inv f := by
    ext j
    simp only [comp_sum, ← Category.assoc, d.inclusion_projection]
    simp [ite_comp]
  map_add' f g := by
    ext i
    exact C.laws.comp_add (d.data.inclusion i) f g
  map_smul' r f := by
    ext i
    exact C.laws.comp_smul r (d.data.inclusion i) f

theorem finrank_homFrom {S X : LinearCategory C} {n : ℕ}
    (d : HomogeneousSum C.data S X n) (U : LinearCategory C) :
    Module.finrank ℝ (X ⟶ U) = n * Module.finrank ℝ (S ⟶ U) := by
  rw [(homFromEquiv C d U).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_hom_of_sums {S X Y : LinearCategory C} {n m : ℕ}
    (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data S Y m) :
    Module.finrank ℝ (X ⟶ Y) = (n * m) * Module.finrank ℝ (End S) := by
  rw [e.finrank_homTo (C := C) X, finrank_homFrom C d S]
  change m * (n * Module.finrank ℝ (End S)) = (n * m) * Module.finrank ℝ (End S)
  ring

/-- Dimensions of the actual tensor Hom agree on homogeneous components. -/
theorem finrank_tensorHom_of_sums {S T X X' Y Y' : LinearCategory C} {n n' m m' : ℕ}
    (d : HomogeneousSum C.data S X n) (d' : HomogeneousSum C.data S X' n')
    (e : HomogeneousSum C.data T Y m) (e' : HomogeneousSum C.data T Y' m')
    (hT : C.data.IsSimple T) :
    Module.finrank ℝ (@Quiver.Hom (LinearCategory C) _ (C.data.tensorObj X Y) (C.data.tensorObj X' Y')) =
      Module.finrank ℝ ((X ⟶ X') ⊗[ℝ] (Y ⟶ Y')) := by
  rw [Module.finrank_tensorProduct,
    finrank_hom_of_sums C (d.tensor e) (d'.tensor e'),
    finrank_tensorEnd C S T hT, finrank_hom_of_sums C d d', finrank_hom_of_sums C e e']
  ring

/-- The given tensor map, rather than a chosen vector-space isomorphism, is bijective. -/
theorem tensorHomLinear_bijective_of_sums {S T X X' Y Y' : LinearCategory C} {n n' m m' : ℕ}
    (d : HomogeneousSum C.data S X n) (d' : HomogeneousSum C.data S X' n')
    (e : HomogeneousSum C.data T Y m) (e' : HomogeneousSum C.data T Y' m')
    (hT : C.data.IsSimple T) : Function.Bijective (tensorHomLinear C X X' Y Y') := by
  refine ⟨tensorHomLinear_injective C X X' Y Y', ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tensorHom_of_sums C d d' e e' hT).symm).mp
      (tensorHomLinear_injective C X X' Y Y')

/-- Each intrinsic type component is the homogeneous span of its chosen simple. -/
theorem tensorHomLinear_bijective_in_components (P : RMod.Classification.PiSuperfusion.{0, 0})
    (hP : ReferenceProperty P.data) {X X' Y Y' : LinearCategory P.toWeaklyPointedSuperfusion}
    {a b : ZMod 8}
    (hX : InComponent P.data.toWeaklyPointedSuperfusionData a X)
    (hX' : InComponent P.data.toWeaklyPointedSuperfusionData a X')
    (hY : InComponent P.data.toWeaklyPointedSuperfusionData b Y)
    (hY' : InComponent P.data.toWeaklyPointedSuperfusionData b Y') :
    Function.Bijective (tensorHomLinear P.toWeaklyPointedSuperfusion X X' Y Y') := by
  obtain ⟨n, ⟨d⟩⟩ := (reference_component_iff_span P hP a X).mp hX
  obtain ⟨n', ⟨d'⟩⟩ := (reference_component_iff_span P hP a X').mp hX'
  obtain ⟨m, ⟨e⟩⟩ := (reference_component_iff_span P hP b Y).mp hY
  obtain ⟨m', ⟨e'⟩⟩ := (reference_component_iff_span P hP b Y').mp hY'
  exact tensorHomLinear_bijective_of_sums P.toWeaklyPointedSuperfusion d d' e e'
    (referenceSimpleRepresentative P hP b).laws.simple

end RMod.BrundanEllis.Stacking.Raw
