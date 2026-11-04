import RMod.Hierarchy.Instances.HomogeneousOperations

/-!
# Coordinates on a homogeneous total Hom submodule

Mathlib's linear inclusion into a product is the inverse to evaluation
on the supported degree. This supplies explicit maps for the comparison
between an enriched category and its recovered presentation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy
variable (C : Supercategory)

def homogeneousEmbedding (X Y : C.data.Obj) (a : ZMod 2) :
    C.data.Hom X Y a →ₗ[ℝ] THom C.data X Y :=
  LinearMap.single ℝ (fun b => C.data.Hom X Y b) a

theorem homogeneousEmbedding_mem (X Y : C.data.Obj) (a : ZMod 2) (f : C.data.Hom X Y a) :
    homogeneousEmbedding C X Y a f ∈ grade C X Y a := by
  intro b hb
  exact Pi.single_eq_of_ne (M := fun b => C.data.Hom X Y b) hb f

def homogeneousGradeEquiv (X Y : C.data.Obj) (a : ZMod 2) :
    C.data.Hom X Y a ≃ₗ[ℝ] grade C X Y a where
  toFun f := ⟨homogeneousEmbedding C X Y a f, homogeneousEmbedding_mem C X Y a f⟩
  invFun f := f.val a
  left_inv f := Pi.single_eq_same (M := fun b => C.data.Hom X Y b) a f
  right_inv f := by
    apply Subtype.ext
    funext b
    by_cases h : b = a
    · subst b
      exact Pi.single_eq_same (M := fun b => C.data.Hom X Y b) a (f.val a)
    · exact (Pi.single_eq_of_ne (M := fun b => C.data.Hom X Y b) h (f.val a)).trans (f.property b h).symm
  map_add' f g := Subtype.ext ((homogeneousEmbedding C X Y a).map_add f g)
  map_smul' r f := Subtype.ext ((homogeneousEmbedding C X Y a).map_smul r f)

theorem homogeneousEmbedding_evaluation {X Y : C.data.Obj} (a : ZMod 2)
    (f : THom C.data X Y) (hf : f ∈ grade C X Y a) :
    homogeneousEmbedding C X Y a (f a) = f :=
  congrArg Subtype.val ((homogeneousGradeEquiv C X Y a).apply_symm_apply ⟨f, hf⟩)

theorem homogeneousEmbedding_comp {X Y Z : C.data.Obj} (a b c : ZMod 2) (hab : a + b = c)
    (f : C.data.Hom X Y a) (g : C.data.Hom Y Z b) :
    tComp C.data (homogeneousEmbedding C X Y a f) (homogeneousEmbedding C Y Z b g) =
      homogeneousEmbedding C X Z c
        (C.data.comp X Y Z c (gradedTmul _ _ a b c hab f g)) := by
  have hf := homogeneousEmbedding_mem C X Y a f
  have hg := homogeneousEmbedding_mem C Y Z b g
  have hc := tComp_mem_grade C _ _ hf hg
  rw [hab] at hc
  apply homogeneous_ext C hc (homogeneousEmbedding_mem C X Z c _)
  rw [tComp_homogeneous_at C a b c hab _ _ hf]
  change C.data.comp X Y Z c (gradedTmul _ _ a b c hab
    (Pi.single (M := fun b => C.data.Hom X Y b) a f a) (Pi.single (M := fun a => C.data.Hom Y Z a) b g b)) = Pi.single (M := fun b => C.data.Hom X Z b) c _ c
  simp only [Pi.single_eq_same]

end RMod.Legacy
