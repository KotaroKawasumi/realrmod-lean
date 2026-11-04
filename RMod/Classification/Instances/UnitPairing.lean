import RMod.Classification.Proofs.Endomorphisms
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The composition pairing at the real unit

Composition is Mathlib's bilinear map. The split-unit algebra equivalence
identifies its values in End(1) with real scalars. No basis, decomposition,
or representative of a simple object enters this definition.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

noncomputable def unitPairing (C : WeaklyPointedSuperfusion.{0, 0}) (V : LinearCategory C) :
    (@Quiver.Hom (LinearCategory C) inferInstance V C.data.tensorUnit) →ₗ[ℝ] (@Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit V) →ₗ[ℝ] ℝ :=
  (CategoryTheory.Linear.comp (S := ℝ) (C := LinearCategory C)
    C.data.tensorUnit V C.data.tensorUnit).flip.compr₂ (unitEndEquiv C).symm.toLinearMap

@[simp]
theorem unitPairing_apply (C : WeaklyPointedSuperfusion.{0, 0}) (V : LinearCategory C)
    (f : @Quiver.Hom (LinearCategory C) inferInstance V C.data.tensorUnit) (g : @Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit V) :
    unitPairing C V f g = (unitEndEquiv C).symm (C.data.comp g f) := rfl

end RMod.Classification
