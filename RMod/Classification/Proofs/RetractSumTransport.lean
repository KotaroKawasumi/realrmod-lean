import RMod.Classification.Instances.RetractSumTransportData
import RMod.Classification.Proofs.SimpleCornerMap

/-!
# Laws for the transported homogeneous presentation

Each target matrix coefficient is the corresponding source corner map.
The target diagonal projector is the ambient image of the source
diagonal projector. These two identities prove all matrix-unit laws and
the total identity while retaining the copied parity sequence.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

theorem endAlgEquiv_map_finSum (C D : WeaklyPointedSuperfusion.{0, 0})
    {X : LinearCategory C} {Y : LinearCategory D} (φ : End X ≃ₐ[ℝ] End Y)
    (n : ℕ) (f : Fin n → End X) :
    φ (C.data.finSum n f) = D.data.finSum n (fun i => φ (f i)) := by
  rw [LinearCategory.finSum_eq_sum C, LinearCategory.finSum_eq_sum D]
  exact map_sum φ f Finset.univ

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C} {Y : LinearCategory D}
  (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
  {n : ℕ} (A : HomogeneousSum C.data d.data.object X n)

theorem retractSumTransport_coefficient (i j : Fin n) :
    D.data.comp (retractSumTransportData C D d.data t.data φ A.data |>.inclusion i)
      (retractSumTransportData C D d.data t.data φ A.data |>.projection j) =
    simpleCornerMap C D d.data t.data φ (C.data.comp (A.data.inclusion i) (A.data.projection j)) := by
  change D.data.comp
    (D.data.comp t.data.inclusion (φ (C.data.comp d.data.projection (A.data.inclusion i))))
    (D.data.comp (φ (C.data.comp (A.data.projection j) d.data.inclusion)) t.data.projection) =
      D.data.comp t.data.inclusion
        (D.data.comp (φ (C.data.comp d.data.projection
          (C.data.comp (C.data.comp (A.data.inclusion i) (A.data.projection j)) d.data.inclusion)))
          t.data.projection)
  rw [D.laws.comp_assoc, ← D.laws.comp_assoc (φ _), ← endAlgEquiv_map_comp C D φ]
  simp only [C.laws.comp_assoc]

variable (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))

include hproj

theorem retractSumTransport_diagonal_projector (i : Fin n) :
    D.data.comp (retractSumTransportData C D d.data t.data φ A.data |>.projection i)
      (retractSumTransportData C D d.data t.data φ A.data |>.inclusion i) =
    φ (C.data.comp (A.data.projection i) (A.data.inclusion i)) := by
  change D.data.comp
    (D.data.comp (φ (C.data.comp (A.data.projection i) d.data.inclusion)) t.data.projection)
    (D.data.comp t.data.inclusion (φ (C.data.comp d.data.projection (A.data.inclusion i)))) = _
  rw [D.laws.comp_assoc, ← D.laws.comp_assoc t.data.projection]
  change D.data.comp (φ (C.data.comp (A.data.projection i) d.data.inclusion))
    (D.data.comp (SimpleRetract.projectorData t.data)
      (φ (C.data.comp d.data.projection (A.data.inclusion i)))) = _
  rw [hproj, ← endAlgEquiv_map_comp C D φ, ← endAlgEquiv_map_comp C D φ]
  apply congrArg φ
  change C.data.comp (C.data.comp (A.data.projection i) d.data.inclusion)
    (C.data.comp (C.data.comp d.data.projection d.data.inclusion)
      (C.data.comp d.data.projection (A.data.inclusion i))) = _
  simp only [C.laws.comp_assoc]
  rw [← C.laws.comp_assoc d.data.inclusion d.data.projection, d.laws.inclusion_projection,
    C.laws.id_comp, ← C.laws.comp_assoc d.data.inclusion d.data.projection,
    d.laws.inclusion_projection, C.laws.id_comp]

theorem retractSumTransportLaws
    (hφ : ∀ {a : ZMod 2} {f : End X}, C.data.IsHomogeneous a f → D.data.IsHomogeneous a (φ f)) :
    HomogeneousSumLaws (retractSumTransportData C D d.data t.data φ A.data) where
  inclusion_grade i := by
    have h := C.laws.comp_grade _ _ d.laws.projection_even (A.laws.inclusion_grade i)
    rw [zero_add] at h
    have hg := D.laws.comp_grade _ _ t.laws.inclusion_even (hφ h)
    rw [zero_add] at hg
    exact hg
  projection_grade i := by
    have h := C.laws.comp_grade _ _ (A.laws.projection_grade i) d.laws.inclusion_even
    rw [add_zero] at h
    have hg := D.laws.comp_grade _ _ (hφ h) t.laws.projection_even
    rw [add_zero] at hg
    exact hg
  diagonal i := (retractSumTransport_coefficient d t φ A i i).trans
    ((congrArg (simpleCornerMap C D d.data t.data φ) (A.laws.diagonal i)).trans
      (simpleCornerMap_id d t φ hproj))
  off_diagonal i j hij := (retractSumTransport_coefficient d t φ A i j).trans
    ((congrArg (simpleCornerMap C D d.data t.data φ) (A.laws.off_diagonal i j hij)).trans
      (map_zero (simpleCornerMap C D d.data t.data φ)))
  total := by
    simp only [retractSumTransport_diagonal_projector d t φ A hproj]
    rw [← endAlgEquiv_map_finSum C D φ, A.laws.total]
    exact map_one φ

end RMod.Classification
