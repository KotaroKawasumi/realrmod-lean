import RMod.Classification.Instances.RightFactorDeletion
import RMod.Classification.Proofs.RightParityComparison
import RMod.Classification.Proofs.HomogeneousIsoCalculus

/-!
# Homogeneous inverse and naturality laws for parity deletion

The degree-zero branch is ordinary unitor naturality. The odd branch
has exactly one crossing with the input map. Consequently deletion and
an equally odd comparison can be composed into an even natural map.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
  {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightFactorDeletion_homogeneousIso (X : C.Obj) (a : ZMod 2) :
    HomogeneousIsoLaws C a (p.rightFactorDeletion X a) := by
  rcases parity_cases a with rfl | rfl
  · exact (EvenIsoLaws.rightUnit hC X).homogeneous
  · exact ⟨hp.rightZ_iso hC X, hp.rightZ_hom_odd hC X, hp.rightZ_inv_odd hC X⟩

theorem rightFactorDeletion_naturality {X Y : C.Obj} {b : ZMod 2} (a : ZMod 2)
    (f : C.Hom X Y) (hf : C.IsHomogeneous b f) :
    C.comp (C.tensorHom f (C.id (p.factor a))) (p.rightFactorDeletion Y a).hom =
      C.smul ((-1 : ℝ) ^ (a * b).val) (C.comp (p.rightFactorDeletion X a).hom f) := by
  rcases parity_cases a with rfl | rfl
  · rw [zero_mul, ZMod.val_zero, pow_zero, hC.one_smul]
    exact hC.right_unitor_naturality f
  · rw [one_mul]
    exact hp.rightZ_naturality hC f hf

end RMod.Classification.PiLaws
