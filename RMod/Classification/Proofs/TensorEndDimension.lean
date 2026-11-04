import RMod.Classification.Proofs.SuperMultiplicity
import RMod.Classification.Instances.HomogeneousSumMap
import RMod.Classification.Instances.TensorEndDualHom
import RMod.Classification.Proofs.Endomorphisms

/-!
# Tensor-endomorphism dimensions from weak invertibility

For a right dual pair Y,Y*, the enriched adjunction measures both End(Y)
and End(X tensor Y) using Y tensor Y*. Its homogeneous unit summands give
the same multiplicity in the two calculations. Thus weak invertibility
alone gives the product formula for total real dimensions.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0})

attribute [local implicit_reducible] CategoryTheory.End
  tensorLeftData tensorRightData tensorLeftSuperfunctor tensorRightSuperfunctor
  Superfunctor.toFunctor

theorem finrank_unitEnd :
    Module.finrank ℝ (End (C := LinearCategory C) C.data.tensorUnit) = 1 := by
  rw [← (unitEndEquiv C).toLinearEquiv.finrank_eq, Module.finrank_self]

theorem finrank_tensor_hom_of_unit_sum {A : LinearCategory C} {n : ℕ}
    (d : HomogeneousSum C.data C.data.tensorUnit A n) (X : LinearCategory C) :
    Module.finrank ℝ (@Quiver.Hom (LinearCategory C) inferInstance X (C.data.tensorObj X A)) =
      n * Module.finrank ℝ (End (C := LinearCategory C) X) := by
  let s := d.map (tensorLeftSuperfunctor C X)
  have h := s.finrank_homTo (C := C) X
  have he := (Linear.homCongr ℝ (Iso.refl (C := LinearCategory C) X)
    ((tensorRightUnitIso C).app X)).finrank_eq
  change Module.finrank ℝ
      (@Quiver.Hom (LinearCategory C) inferInstance X (C.data.tensorObj X C.data.tensorUnit)) =
    Module.finrank ℝ (End (C := LinearCategory C) X) at he
  change Module.finrank ℝ
      (@Quiver.Hom (LinearCategory C) inferInstance X (C.data.tensorObj X A)) =
    n * Module.finrank ℝ
      (@Quiver.Hom (LinearCategory C) inferInstance X (C.data.tensorObj X C.data.tensorUnit)) at h
  exact h.trans (congrArg (n * ·) he)

theorem finrank_tensorEnd_of_weaklyInvertible (X Y : LinearCategory C)
    (hY : C.data.IsWeaklyInvertible Y) :
    Module.finrank ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) =
      Module.finrank ℝ (End (C := LinearCategory C) X) *
        Module.finrank ℝ (End (C := LinearCategory C) Y) := by
  obtain ⟨R, hp, p, q, _, hm⟩ := hY
  obtain ⟨pair⟩ := (hasExactPairing_iff C Y R).mp hp
  obtain ⟨d⟩ := exists_homogeneousSum_of_superMultiplicity C hm
  have hn : Module.finrank ℝ (End (C := LinearCategory C) Y) = p + q := by
    calc
      _ = Module.finrank ℝ (@Quiver.Hom (LinearCategory C) inferInstance
          C.data.tensorUnit (C.data.tensorObj Y R)) := pair.rightEndHomLinearEquiv.finrank_eq
      _ = (p + q) * Module.finrank ℝ (End (C := LinearCategory C) C.data.tensorUnit) :=
        d.finrank_homTo (C := C) C.data.tensorUnit
      _ = p + q := by rw [finrank_unitEnd, mul_one]
  calc
    _ = Module.finrank ℝ (@Quiver.Hom (LinearCategory C) inferInstance X
        (C.data.tensorObj X (C.data.tensorObj Y R))) := (pair.tensorEndHomLinearEquiv X).finrank_eq
    _ = (p + q) * Module.finrank ℝ (End (C := LinearCategory C) X) :=
      finrank_tensor_hom_of_unit_sum C d X
    _ = _ := by rw [hn, Nat.mul_comm]

theorem finrank_tensorEnd (X Y : LinearCategory C) (hY : C.data.IsSimple Y) :
    Module.finrank ℝ (End (C := LinearCategory C) (C.data.tensorObj X Y)) =
      Module.finrank ℝ (End (C := LinearCategory C) X) *
        Module.finrank ℝ (End (C := LinearCategory C) Y) :=
  finrank_tensorEnd_of_weaklyInvertible C X Y (C.laws.weakly_pointed Y hY)

end RMod.Classification
