import RMod.Hierarchy.Bridge.LegacyTensor

/-!
# Total naturality after the convention correction

The Koszul correction is a degree-two cocycle. Its two scalar factors
therefore agree on the two sides of associator naturality. The unitors
involve an even identity and need no correction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

theorem legacyAssociatorNaturality_homogeneous {X X' Y Y' Z Z' : C.data.Obj}
    (a b c : ZMod 2) (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (h : THom C.super.data Z Z')
    (hf : f ∈ grade C.super X X' a) (hg : g ∈ grade C.super Y Y' b)
    (hh : h ∈ grade C.super Z Z' c) :
    tComp C.super.data (legacyTensor C (legacyTensor C f g) h)
      (evenPoint (C.data.monoidal.associatorHom X' Y' Z')) =
    tComp C.super.data (evenPoint (C.data.monoidal.associatorHom X Y Z))
      (legacyTensor C f (legacyTensor C g h)) := by
  rw [legacyTensor_homogeneous C (a + b) c (legacyTensor C f g) h
      (legacyTensor_mem_grade C f g hf hg) hh,
    legacyTensor_homogeneous C a (b + c) f (legacyTensor C g h)
      hf (legacyTensor_mem_grade C g h hg hh),
    legacyTensor_homogeneous C a b f g hf hg,
    legacyTensor_homogeneous C b c g h hg hh,
    tTensor_smul_left, tTensor_smul_right, tComp_smul_left, tComp_smul_right,
    tComp_smul_left, tComp_smul_right]
  simp only [smul_smul]
  erw [C.laws.monoidal.associator_naturality f g h]
  congr 1
  rcases Classification.parity_cases a with rfl | rfl <;>
    rcases Classification.parity_cases b with rfl | rfl <;>
    rcases Classification.parity_cases c with rfl | rfl <;>
    norm_num [ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_one]

theorem legacyAssociatorNaturality {X X' Y Y' Z Z' : C.data.Obj}
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (h : THom C.super.data Z Z') :
    tComp C.super.data (legacyTensor C (legacyTensor C f g) h)
      (evenPoint (C.data.monoidal.associatorHom X' Y' Z')) =
    tComp C.super.data (evenPoint (C.data.monoidal.associatorHom X Y Z))
      (legacyTensor C f (legacyTensor C g h)) := by
  have hs (a b c : ZMod 2) := legacyAssociatorNaturality_homogeneous C a b c
    (homogeneousPart C.super a f) (homogeneousPart C.super b g) (homogeneousPart C.super c h)
    (homogeneousPart_mem C.super a f) (homogeneousPart_mem C.super b g)
    (homogeneousPart_mem C.super c h)
  rw [← homogeneousPart_add C.super f, ← homogeneousPart_add C.super g,
    ← homogeneousPart_add C.super h]
  simp only [legacyTensor_add_left, legacyTensor_add_right, tComp_add_left, tComp_add_right]
  rw [hs 0 0 0, hs 0 0 1, hs 0 1 0, hs 0 1 1, hs 1 0 0, hs 1 0 1, hs 1 1 0, hs 1 1 1]

theorem legacyLeftNaturality {X Y : C.data.Obj} (f : THom C.super.data X Y) :
    tComp C.super.data
      (legacyTensor C (evenPoint (C.data.id C.data.monoidal.unit)) f)
      (evenPoint (C.data.monoidal.leftHom Y)) =
    tComp C.super.data (evenPoint (C.data.monoidal.leftHom X)) f := by
  rw [legacyTensor_even_left C _ _ (evenPoint_mem_grade C.super _)]
  exact C.laws.monoidal.left_naturality f

theorem legacyRightNaturality {X Y : C.data.Obj} (f : THom C.super.data X Y) :
    tComp C.super.data
      (legacyTensor C f (evenPoint (C.data.id C.data.monoidal.unit)))
      (evenPoint (C.data.monoidal.rightHom Y)) =
    tComp C.super.data (evenPoint (C.data.monoidal.rightHom X)) f := by
  rw [legacyTensor_even_right C _ _ (evenPoint_mem_grade C.super _)]
  exact C.laws.monoidal.right_naturality f

end RMod.Legacy.Hierarchy
