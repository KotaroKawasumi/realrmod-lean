import RMod.Hierarchy.Bridge.LegacyData

/-!
# The inverse tensor convention correction

The legacy tensor is bilinear, preserves degrees, and agrees with the
chronological tensor whenever one input is even. On homogeneous inputs
the correction is precisely the Koszul sign of their two degrees.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

private theorem part_add {X Y : C.data.Obj} (a : ZMod 2)
    (f g : THom C.super.data X Y) :
    homogeneousPart C.super a (f + g) = homogeneousPart C.super a f + homogeneousPart C.super a g := by
  funext b
  change (if b = a then f b + g b else 0) =
    (if b = a then f b else 0) + (if b = a then g b else 0)
  split_ifs <;> simp

private theorem part_smul {X Y : C.data.Obj} (a : ZMod 2) (r : ℝ)
    (f : THom C.super.data X Y) :
    homogeneousPart C.super a (r • f) = r • homogeneousPart C.super a f := by
  funext b
  change (if b = a then r • f b else 0) = r • (if b = a then f b else 0)
  split_ifs <;> simp

private theorem part_mem {X Y : C.data.Obj} (a b : ZMod 2)
    (f : THom C.super.data X Y) (hf : f ∈ grade C.super X Y a) :
    homogeneousPart C.super b f ∈ grade C.super X Y a := by
  intro c hc
  simp [homogeneousPart, hf c hc]

private theorem part_eq {X Y : C.data.Obj} (a : ZMod 2)
    (f : THom C.super.data X Y) (hf : f ∈ grade C.super X Y a) :
    homogeneousPart C.super a f = f := by
  funext b
  by_cases h : b = a
  · simp [homogeneousPart, h]
  · simp [homogeneousPart, h, hf b h]

private theorem part_zero {X Y : C.data.Obj} {a b : ZMod 2} (hab : b ≠ a)
    (f : THom C.super.data X Y) (hf : f ∈ grade C.super X Y a) :
    homogeneousPart C.super b f = 0 := by
  funext c
  by_cases h : c = b
  · subst c
    simp [homogeneousPart, hf b hab]
  · simp [homogeneousPart, h]

theorem legacyTensor_add_left {X X' Y Y' : C.data.Obj}
    (f f' : THom C.super.data X X') (g : THom C.super.data Y Y') :
    legacyTensor C (f + f') g = legacyTensor C f g + legacyTensor C f' g := by
  simp only [legacyTensor, part_add, tTensor_add_left, smul_add]
  abel

theorem legacyTensor_add_right {X X' Y Y' : C.data.Obj}
    (f : THom C.super.data X X') (g g' : THom C.super.data Y Y') :
    legacyTensor C f (g + g') = legacyTensor C f g + legacyTensor C f g' := by
  simp only [legacyTensor, part_add, tTensor_add_right, smul_add]
  abel

theorem legacyTensor_smul_left {X X' Y Y' : C.data.Obj} (r : ℝ)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y') :
    legacyTensor C (r • f) g = r • legacyTensor C f g := by
  simp only [legacyTensor, part_smul, tTensor_smul_left, smul_sub, smul_smul, mul_comm (2 : ℝ)]

theorem legacyTensor_smul_right {X X' Y Y' : C.data.Obj} (r : ℝ)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y') :
    legacyTensor C f (r • g) = r • legacyTensor C f g := by
  simp only [legacyTensor, part_smul, tTensor_smul_right, smul_sub, smul_smul, mul_comm (2 : ℝ)]

theorem legacyTensor_mem_grade {X X' Y Y' : C.data.Obj} {a b : ZMod 2}
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (hf : f ∈ grade C.super X X' a) (hg : g ∈ grade C.super Y Y' b) :
    legacyTensor C f g ∈ grade C.super (C.data.monoidal.tensor.obj (X, Y))
      (C.data.monoidal.tensor.obj (X', Y')) (a + b) :=
  Submodule.sub_mem _ (tTensor_mem_grade _ _ f g hf hg)
    (Submodule.smul_mem _ _ (tTensor_mem_grade _ _ _ _
      (part_mem C a 1 f hf) (part_mem C b 1 g hg)))

theorem legacyTensor_even_left {X X' Y Y' : C.data.Obj}
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (hf : f ∈ grade C.super X X' 0) : legacyTensor C f g = tTensor C.data.monoidal f g := by
  rw [legacyTensor, part_zero C one_ne_zero f hf, tTensor_zero_left, smul_zero, sub_zero]

theorem legacyTensor_even_right {X X' Y Y' : C.data.Obj}
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (hg : g ∈ grade C.super Y Y' 0) : legacyTensor C f g = tTensor C.data.monoidal f g := by
  rw [legacyTensor, part_zero C one_ne_zero g hg, tTensor_zero_right, smul_zero, sub_zero]

theorem legacyTensor_homogeneous {X X' Y Y' : C.data.Obj} (a b : ZMod 2)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (hf : f ∈ grade C.super X X' a) (hg : g ∈ grade C.super Y Y' b) :
    legacyTensor C f g = (-1 : ℝ) ^ (a * b).val • tTensor C.data.monoidal f g := by
  rcases Classification.parity_cases a with rfl | rfl
  · simpa using legacyTensor_even_left C f g hf
  · rcases Classification.parity_cases b with rfl | rfl
    · simpa using legacyTensor_even_right C f g hg
    · rw [legacyTensor, part_eq C 1 f hf, part_eq C 1 g hg]
      simp only [mul_one, ZMod.val_one, pow_one, neg_one_smul, two_smul ℝ]
      abel

end RMod.Legacy.Hierarchy
