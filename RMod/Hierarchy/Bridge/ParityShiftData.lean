import RMod.Hierarchy.Abstract.ParityShift
import RMod.Hierarchy.Bridge.Superfunctors
import RMod.Classification.Instances.TensorFunctors
import RMod.Classification.Proofs.Pi

/-!
# The old parity object supplies the new parity shift

Tensoring on the left by the specified parity object is the shift functor.
The old odd comparison and its inverse supply the components; the inverse
naturality formula is derived from their existing inverse equations.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0}) (p : Classification.Pi C.data)

def ofOldParityShiftData : ParityShiftData (ofOldSupercategoryData C) where
  functor := ofOldSuperfunctorData (Classification.tensorLeftSuperfunctor C p.data.object)
  hom X := homogeneousMap _ 1 ⟨p.data.zInv X, p.laws.z_inv_odd C.laws X⟩
  inv X := homogeneousMap _ 1 ⟨p.data.zHom X, p.laws.z_hom_odd C.laws X⟩

theorem oldParity_inverse_naturality {X Y : C.data.Obj} (a : ZMod 2)
    (f : C.data.Hom X Y) (hf : C.data.IsHomogeneous a f) :
    C.data.comp (p.data.zInv X) (p.data.shiftHom f) =
      C.data.smul ((-1 : ℝ) ^ a.val) (C.data.comp f (p.data.zInv Y)) := by
  have h := p.laws.z_naturality C.laws f hf
  have hi := (p.laws.z_iso C.laws X).inv_hom
  have hj := (p.laws.z_iso C.laws Y).hom_inv
  calc
    _ = C.data.comp (C.data.comp (p.data.zInv X)
        (C.data.comp (p.data.shiftHom f) (p.data.zHom Y))) (p.data.zInv Y) := by
      rw [C.laws.comp_assoc, C.laws.comp_assoc, hj, C.laws.comp_id]
    _ = _ := by
      rw [h, C.laws.comp_smul, C.laws.smul_comp, ← C.laws.comp_assoc,
        hi, C.laws.id_comp]

theorem totalHomEquiv_homogeneousMap (X Y : C.data.Obj) (a : ZMod 2)
    (f : Classification.LinearCategory.grade C X Y a) :
    totalHomEquiv C X Y (homogeneousPoint a (homogeneousMap (oldEnrichedHom C X Y) a f)) = f.val := by
  rcases Classification.parity_cases a with rfl | rfl
  · erw [totalHomEquiv_apply, homogeneousPoint_map_same,
      homogeneousPoint_map_ne _ _ _ _ one_ne_zero]
    exact C.laws.add_zero _
  · erw [totalHomEquiv_apply, homogeneousPoint_map_same,
      homogeneousPoint_map_ne _ _ _ _ zero_ne_one]
    exact C.laws.zero_add _

end RMod.Legacy.Hierarchy
