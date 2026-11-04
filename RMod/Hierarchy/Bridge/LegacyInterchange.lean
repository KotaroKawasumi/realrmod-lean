import RMod.Hierarchy.Bridge.LegacyTensor
import RMod.Hierarchy.Instances.TotalInterchange

/-!
# Super-interchange in the legacy convention

Applying the same Koszul correction twice restores the old crossing
convention. Bilinearity extends the four-homogeneous-input calculation to
the legacy law, which assumes homogeneity of only the crossed inputs.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

theorem legacyTensor_interchange_homogeneous {X X' X'' Y Y' Y'' : C.data.Obj}
    (i j k l : ZMod 2)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (q : THom C.super.data X' X'') (r : THom C.super.data Y' Y'')
    (hf : f ∈ grade C.super X X' i) (hg : g ∈ grade C.super Y Y' j)
    (hq : q ∈ grade C.super X' X'' k) (hr : r ∈ grade C.super Y' Y'' l) :
    tComp C.super.data (legacyTensor C f g) (legacyTensor C q r) =
      (-1 : ℝ) ^ (l * i).val •
        legacyTensor C (tComp C.super.data f q) (tComp C.super.data g r) := by
  rw [legacyTensor_homogeneous C i j f g hf hg,
    legacyTensor_homogeneous C k l q r hq hr,
    legacyTensor_homogeneous C (i + k) (j + l) _ _
      (tComp_mem_grade C.super f q hf hq) (tComp_mem_grade C.super g r hg hr),
    tComp_smul_left, tComp_smul_right, tTensor_interchange C i j k l f g q r hf hg hq hr]
  simp only [smul_smul]
  congr 1
  rcases Classification.parity_cases i with rfl | rfl <;>
    rcases Classification.parity_cases j with rfl | rfl <;>
    rcases Classification.parity_cases k with rfl | rfl <;>
    rcases Classification.parity_cases l with rfl | rfl <;>
    norm_num [ZMod.val_natCast, ZMod.val_ofNat, ZMod.val_one]

theorem legacyTensor_interchange {X X' X'' Y Y' Y'' : C.data.Obj}
    (i l : ZMod 2)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (q : THom C.super.data X' X'') (r : THom C.super.data Y' Y'')
    (hf : f ∈ grade C.super X X' i) (hr : r ∈ grade C.super Y' Y'' l) :
    tComp C.super.data (legacyTensor C f g) (legacyTensor C q r) =
      (-1 : ℝ) ^ (l * i).val •
        legacyTensor C (tComp C.super.data f q) (tComp C.super.data g r) := by
  rw [← homogeneousPart_add C.super g, ← homogeneousPart_add C.super q]
  simp only [legacyTensor_add_left, legacyTensor_add_right, tComp_add_left, tComp_add_right, smul_add]
  rw [legacyTensor_interchange_homogeneous C i 0 0 l _ _ _ _ hf
        (homogeneousPart_mem C.super 0 g) (homogeneousPart_mem C.super 0 q) hr,
    legacyTensor_interchange_homogeneous C i 0 1 l _ _ _ _ hf
        (homogeneousPart_mem C.super 0 g) (homogeneousPart_mem C.super 1 q) hr,
    legacyTensor_interchange_homogeneous C i 1 0 l _ _ _ _ hf
        (homogeneousPart_mem C.super 1 g) (homogeneousPart_mem C.super 0 q) hr,
    legacyTensor_interchange_homogeneous C i 1 1 l _ _ _ _ hf
        (homogeneousPart_mem C.super 1 g) (homogeneousPart_mem C.super 1 q) hr]
  abel

end RMod.Legacy.Hierarchy
