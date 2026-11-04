import RMod.Classification.Instances.BiproductMap
import RMod.Classification.Proofs.FiniteSumCalculus
import RMod.Classification.Proofs.Decompositions

/-!
# Laws for summing a family of morphisms

The inclusion and projection equations determine the sum map. They give
identity and composition, while bilinearity and the homogeneous sum
calculus give linearity and parity preservation on the complete Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification.Biproduct

variable {C : PiSuperfusionData.{0, 0}}
  (hC : WeaklyPointedSuperfusionLaws C.toWeaklyPointedSuperfusionData)
  {n : ℕ} {S T U : Fin n → C.Obj}

include hC

theorem inclusion_mapHom (b : Biproduct C S) (c : Biproduct C T)
    (f : (i : Fin n) → C.Hom (S i) (T i)) (i : Fin n) :
    C.comp (b.data.inclusion i) (b.data.mapHom c.data f) = C.comp (f i) (c.data.inclusion i) := by
  unfold BiproductData.mapHom
  rw [raw_comp_finSum hC]
  have he (j : Fin n) :
      C.comp (b.data.inclusion i) (C.comp (C.comp (b.data.projection j) (f j)) (c.data.inclusion j)) =
        if j = i then C.comp (f i) (c.data.inclusion i) else C.zero := by
    by_cases h : j = i
    · subst j
      simp only [ite_true, ← hC.comp_assoc, b.laws.diagonal, hC.id_comp]
    · simp only [if_neg h, ← hC.comp_assoc, b.laws.off_diagonal i j (Ne.symm h), raw_zero_comp hC]
  simp only [he]
  exact raw_finSum_single hC i _

theorem mapHom_projection (b : Biproduct C S) (c : Biproduct C T)
    (f : (i : Fin n) → C.Hom (S i) (T i)) (j : Fin n) :
    C.comp (b.data.mapHom c.data f) (c.data.projection j) = C.comp (b.data.projection j) (f j) := by
  unfold BiproductData.mapHom
  rw [raw_finSum_comp hC]
  have he (i : Fin n) :
      C.comp (C.comp (C.comp (b.data.projection i) (f i)) (c.data.inclusion i)) (c.data.projection j) =
        if i = j then C.comp (b.data.projection j) (f j) else C.zero := by
    by_cases h : i = j
    · subst i
      simp only [ite_true, hC.comp_assoc, c.laws.diagonal, hC.comp_id]
    · simp only [if_neg h, hC.comp_assoc, c.laws.off_diagonal i j h, raw_comp_zero hC]
  simp only [he]
  exact raw_finSum_single hC j _

theorem mapHom_id (b : Biproduct C S) :
    b.data.mapHom b.data (fun i => C.id (S i)) = C.id b.data.object := by
  apply hom_ext_of_inclusions hC b.data.inclusion b.data.projection b.laws.total
  intro i
  rw [inclusion_mapHom hC, hC.id_comp, hC.comp_id]

theorem mapHom_comp (b : Biproduct C S) (c : Biproduct C T) (d : Biproduct C U)
    (f : (i : Fin n) → C.Hom (S i) (T i)) (g : (i : Fin n) → C.Hom (T i) (U i)) :
    C.comp (b.data.mapHom c.data f) (c.data.mapHom d.data g) =
      b.data.mapHom d.data (fun i => C.comp (f i) (g i)) := by
  apply hom_ext_of_inclusions hC b.data.inclusion b.data.projection b.laws.total
  intro i
  rw [← hC.comp_assoc, inclusion_mapHom hC, hC.comp_assoc, inclusion_mapHom hC,
    inclusion_mapHom hC, hC.comp_assoc]

theorem mapHom_grade (b : Biproduct C S) (c : Biproduct C T) (a : ZMod 2)
    (f : (i : Fin n) → C.Hom (S i) (T i)) (hf : ∀ i, C.IsHomogeneous a (f i)) :
    C.IsHomogeneous a (b.data.mapHom c.data f) := by
  apply raw_finSum_grade hC
  intro i
  have h := hC.comp_grade _ _
    (hC.comp_grade _ _ (b.laws.projection_even i) (hf i)) (c.laws.inclusion_even i)
  change C.IsHomogeneous ((0 + a) + 0) _ at h
  simpa only [zero_add, add_zero] using h

theorem mapHom_zero (b : Biproduct C S) (c : Biproduct C T) :
    b.data.mapHom c.data (fun _ => C.zero) = C.zero := by
  simp only [BiproductData.mapHom, raw_comp_zero hC, raw_zero_comp hC, raw_finSum_zero hC]

theorem mapHom_add (b : Biproduct C S) (c : Biproduct C T)
    (f g : (i : Fin n) → C.Hom (S i) (T i)) :
    b.data.mapHom c.data (fun i => C.add (f i) (g i)) =
      C.add (b.data.mapHom c.data f) (b.data.mapHom c.data g) := by
  simp only [BiproductData.mapHom, hC.comp_add, hC.add_comp, raw_finSum_add hC]

theorem mapHom_smul (b : Biproduct C S) (c : Biproduct C T)
    (r : ℝ) (f : (i : Fin n) → C.Hom (S i) (T i)) :
    b.data.mapHom c.data (fun i => C.smul r (f i)) = C.smul r (b.data.mapHom c.data f) := by
  simp only [BiproductData.mapHom, hC.comp_smul, hC.smul_comp, raw_finSum_smul hC]

end RMod.Classification.Biproduct
