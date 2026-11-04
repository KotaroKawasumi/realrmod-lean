import RMod.Classification.Instances.UnitPairing
import RMod.Classification.Proofs.UnitSplitting

/-!
# Perfection of composition at the split unit

The section and retraction results detect the kernel in both variables.
Mathlib's finite-dimensional perfect-pairing theorem upgrades these two
injectivity statements to linear equivalences with the dual spaces. In
particular every functional on Hom(1,V) is represented by an actual cap.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) (V : LinearCategory C)

theorem unitPairing_injective : Function.Injective (unitPairing C V) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  by_contra hne
  obtain ⟨g, hg⟩ := unit_section C f hne
  have he := DFunLike.congr_fun hf g
  change (unitEndEquiv C).symm (C.data.comp g f) = 0 at he
  rw [hg] at he
  change (unitEndEquiv C).symm 1 = 0 at he
  rw [map_one] at he
  exact one_ne_zero he

theorem unitPairing_flip_injective : Function.Injective (unitPairing C V).flip := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  by_contra hne
  obtain ⟨g, hg⟩ := unit_retraction C f hne
  have he := DFunLike.congr_fun hf g
  change (unitEndEquiv C).symm (C.data.comp f g) = 0 at he
  rw [hg] at he
  change (unitEndEquiv C).symm 1 = 0 at he
  rw [map_one] at he
  exact one_ne_zero he

instance unitPairing_isPerfPair : (unitPairing C V).IsPerfPair :=
  LinearMap.IsPerfPair.of_injective (unitPairing_injective C V) (unitPairing_flip_injective C V)

/-- The representing cap is obtained from the proved perfect pairing. -/
theorem exists_cap_functional (φ : Module.Dual ℝ (@Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit V)) :
    ∃ cap : @Quiver.Hom (LinearCategory C) inferInstance V C.data.tensorUnit, ∀ f : @Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit V,
      C.data.comp f cap = C.data.smul (φ f) (C.data.id C.data.tensorUnit) := by
  let cap := (unitPairing C V).toPerfPair.symm φ
  refine ⟨cap, fun f => ?_⟩
  have h := DFunLike.congr_fun ((unitPairing C V).apply_symm_toPerfPair_self φ) f
  apply (unitEndEquiv C).symm.injective
  change unitPairing C V cap f = (unitEndEquiv C).symm (unitEndEquiv C (φ f))
  rw [AlgEquiv.symm_apply_apply]
  exact h

end RMod.Classification
