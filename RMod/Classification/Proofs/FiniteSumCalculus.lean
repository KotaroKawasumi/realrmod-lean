import RMod.Classification.Proofs.Grading

/-!
# Mathlib finite-sum identities for the raw operations

These adapters use the existing equality between the stored finite sum
and Mathlib's sum in the full real Hom space. They provide the scalar,
additive, homogeneous and single-coordinate identities needed to assemble
maps of the chosen convolution sums.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem raw_finSum_add {X Y : C.Obj} (n : ℕ) (f g : Fin n → C.Hom X Y) :
    C.finSum n (fun i => C.add (f i) (g i)) = C.add (C.finSum n f) (C.finSum n g) := by
  letI : AddCommGroup (C.Hom X Y) := (LinearCategory.preadditive ⟨C, hC⟩).homGroup X Y
  simp only [LinearCategory.finSum_eq_sum ⟨C, hC⟩ (X := X) (Y := Y)]
  exact Finset.sum_add_distrib

theorem raw_finSum_smul {X Y : C.Obj} (n : ℕ) (r : ℝ) (f : Fin n → C.Hom X Y) :
    C.finSum n (fun i => C.smul r (f i)) = C.smul r (C.finSum n f) := by
  letI : AddCommGroup (C.Hom X Y) := (LinearCategory.preadditive ⟨C, hC⟩).homGroup X Y
  letI : Module ℝ (C.Hom X Y) := (LinearCategory.linear ⟨C, hC⟩).homModule X Y
  simp only [LinearCategory.finSum_eq_sum ⟨C, hC⟩ (X := X) (Y := Y)]
  exact (Finset.smul_sum (r := r) (f := f) (s := Finset.univ)).symm

theorem raw_finSum_grade {X Y : C.Obj} (n : ℕ) (a : ZMod 2) (f : Fin n → C.Hom X Y)
    (hf : ∀ i, C.IsHomogeneous a (f i)) : C.IsHomogeneous a (C.finSum n f) := by
  letI : AddCommGroup (C.Hom X Y) := (LinearCategory.preadditive ⟨C, hC⟩).homGroup X Y
  letI : Module ℝ (C.Hom X Y) := (LinearCategory.linear ⟨C, hC⟩).homModule X Y
  change C.finSum n f ∈ LinearCategory.grade ⟨C, hC⟩ X Y a
  rw [LinearCategory.finSum_eq_sum ⟨C, hC⟩ (X := X) (Y := Y)]
  exact Submodule.sum_mem _ (fun i _ => hf i)

theorem raw_finSum_single {X Y : C.Obj} {n : ℕ} (i : Fin n) (f : C.Hom X Y) :
    C.finSum n (fun j => if j = i then f else C.zero) = f := by
  letI : AddCommGroup (C.Hom X Y) := (LinearCategory.preadditive ⟨C, hC⟩).homGroup X Y
  rw [LinearCategory.finSum_eq_sum ⟨C, hC⟩ (X := X) (Y := Y)]
  change (∑ j : Fin n, if j = i then (f : @Quiver.Hom (LinearCategory ⟨C, hC⟩) _ X Y) else 0) = f
  simp

end RMod.Classification
