import RMod.Classification.Proofs.Grading
import RMod.Classification.Abstract.Equivalence

/-!
# Tensor calculus when a crossing factor is even

The signed interchange axiom initially asks for homogeneous crossing
factors. Bilinearity extends its sign-free specialization to arbitrary
morphisms whenever either crossing factor is even. This is needed for
naturality on all morphisms in inverse superfunctors and in dual adjunctions.
-/

set_option autoImplicit false
universe u v u' v'

namespace RMod.Classification

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C)

include hC

theorem comp_even {X Y Z : C.Obj} {f : C.Hom X Y} {g : C.Hom Y Z}
    (hf : C.IsHomogeneous 0 f) (hg : C.IsHomogeneous 0 g) : C.IsHomogeneous 0 (C.comp f g) := by
  have h := hC.comp_grade f g hf hg
  rw [zero_add] at h
  exact h

theorem tensor_even {X Y Z W : C.Obj} {f : C.Hom X Y} {g : C.Hom Z W}
    (hf : C.IsHomogeneous 0 f) (hg : C.IsHomogeneous 0 g) :
    C.IsHomogeneous 0 (C.tensorHom f g) := by
  have h := hC.tensor_grade f g hf hg
  rw [zero_add] at h
  exact h

theorem tensor_zero_left {X₁ Y₁ X₂ Y₂ : C.Obj} (g : C.Hom X₂ Y₂) :
    C.tensorHom (C.zero : C.Hom X₁ Y₁) g = C.zero := by
  calc
    _ = C.tensorHom (C.smul 0 (C.zero : C.Hom X₁ Y₁)) g := by rw [hC.smul_zero]
    _ = C.zero := by rw [hC.tensor_smul_left, hC.zero_smul]

theorem tensor_zero_right {X₁ Y₁ X₂ Y₂ : C.Obj} (f : C.Hom X₁ Y₁) :
    C.tensorHom f (C.zero : C.Hom X₂ Y₂) = C.zero := by
  calc
    _ = C.tensorHom f (C.smul 0 (C.zero : C.Hom X₂ Y₂)) := by rw [hC.smul_zero]
    _ = C.zero := by rw [hC.tensor_smul_right, hC.zero_smul]

theorem interchange_second_even {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C.Obj}
    (f : C.Hom Y₁ Z₁) (g : C.Hom Y₂ Z₂) (h : C.Hom X₁ Y₁) (k : C.Hom X₂ Y₂)
    (hg : C.IsHomogeneous 0 g) :
    C.comp (C.tensorHom h k) (C.tensorHom f g) =
      C.tensorHom (C.comp h f) (C.comp k g) := by
  have hh : ∀ {a} (h' : C.Hom X₁ Y₁), C.IsHomogeneous a h' →
      C.comp (C.tensorHom h' k) (C.tensorHom f g) =
        C.tensorHom (C.comp h' f) (C.comp k g) := by
    intro a h' hmem
    rw [hC.super_interchange f g h' k hg hmem]
    simp only [zero_mul, ZMod.val_zero, pow_zero, hC.one_smul]
  obtain ⟨h₀, h₁, h₀mem, h₁mem, he⟩ := hC.grade_decomposition h
  rw [← he]
  simp only [hC.tensor_add_left, hC.add_comp, hh h₀ h₀mem, hh h₁ h₁mem]

theorem interchange_first_even {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C.Obj}
    (f : C.Hom Y₁ Z₁) (g : C.Hom Y₂ Z₂) (h : C.Hom X₁ Y₁) (k : C.Hom X₂ Y₂)
    (hh : C.IsHomogeneous 0 h) :
    C.comp (C.tensorHom h k) (C.tensorHom f g) =
      C.tensorHom (C.comp h f) (C.comp k g) := by
  have hg : ∀ {a} (g' : C.Hom Y₂ Z₂), C.IsHomogeneous a g' →
      C.comp (C.tensorHom h k) (C.tensorHom f g') =
        C.tensorHom (C.comp h f) (C.comp k g') := by
    intro a g' hmem
    rw [hC.super_interchange f g' h k hmem hh]
    simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul]
  obtain ⟨g₀, g₁, g₀mem, g₁mem, he⟩ := hC.grade_decomposition g
  rw [← he]
  simp only [hC.tensor_add_right, hC.comp_add, hg g₀ g₀mem, hg g₁ g₁mem]

omit hC in
/-- Naturality of the inverse tensorator also holds on odd morphisms. -/
theorem MonoidalSuperfunctorLaws.tensor_inv_naturality
    {B : WeaklyPointedSuperfusionData.{u', v'}} (hB : WeaklyPointedSuperfusionLaws B)
    {F : MonoidalSuperfunctorData C B} (hF : MonoidalSuperfunctorLaws C B F)
    {X X' Y Y' : C.Obj} (f : C.Hom X X') (g : C.Hom Y Y') :
    B.comp (F.map (C.tensorHom f g)) (F.tensorInv X' Y') =
      B.comp (F.tensorInv X Y) (B.tensorHom (F.map f) (F.map g)) := by
  calc
    _ = B.comp (B.comp (F.tensorInv X Y) (F.tensorHom X Y))
        (B.comp (F.map (C.tensorHom f g)) (F.tensorInv X' Y')) := by
      rw [hF.tensor_inv_hom, hB.id_comp]
    _ = B.comp (F.tensorInv X Y)
        (B.comp (B.comp (F.tensorHom X Y) (F.map (C.tensorHom f g)))
          (F.tensorInv X' Y')) := by simp only [hB.comp_assoc]
    _ = _ := by
      rw [← hF.tensor_naturality, hB.comp_assoc, hF.tensor_hom_inv, hB.comp_id]

end RMod.Classification
