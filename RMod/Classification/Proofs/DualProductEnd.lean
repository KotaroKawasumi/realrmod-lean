import RMod.Classification.Instances.EndDualHom
import RMod.Classification.Proofs.TensorEndSurjection
import RMod.Classification.Proofs.UnitMatrixCenter

/-!
# Endomorphisms of the weak-inverse dual product

The two enriched adjunctions identify End(X) and End(Y) with the same
space Hom(1,X tensor Y). If this dual product is a homogeneous unit sum,
its matrix dimension gives surjectivity of tensoring endomorphisms without
first assuming that the selected dual Y is simple or weakly invertible.
-/

set_option autoImplicit false

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X Y : LinearCategory C} (p : DualPairing C X Y)

attribute [local implicit_reducible] CategoryTheory.End

include p
theorem finrank_end_eq : Module.finrank ℝ (End (C := LinearCategory C) X) =
    Module.finrank ℝ (End (C := LinearCategory C) Y) :=
  p.rightEndHomLinearEquiv.finrank_eq.trans p.endHomLinearEquiv.finrank_eq.symm

theorem tensorEnd_bijective_of_unit_sum {n : ℕ}
    (d : HomogeneousSum C.data C.data.tensorUnit (C.data.tensorObj X Y) n) :
    Function.Bijective (tensorEndLinear C X Y) := by
  have hn : Module.finrank ℝ (End (C := LinearCategory C) X) = n := by
    have h := d.finrank_homTo (C := C) C.data.tensorUnit
    change Module.finrank ℝ (@Quiver.Hom (LinearCategory C) inferInstance
        C.data.tensorUnit (C.data.tensorObj X Y)) =
      n * Module.finrank ℝ (End (C := LinearCategory C) C.data.tensorUnit) at h
    rw [finrank_unitEnd, mul_one] at h
    exact p.rightEndHomLinearEquiv.finrank_eq.trans h
  apply tensorEndLinear_bijective_of_finrank C X Y
  rw [d.finrank_end (C := C), finrank_unitEnd, mul_one, ← p.finrank_end_eq, hn]

end RMod.Classification.DualPairing
