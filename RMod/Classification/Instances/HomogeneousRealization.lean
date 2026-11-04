import RMod.Classification.Abstract.HomogeneousRealization
import RMod.Classification.Proofs.IntrinsicTypes

/-!
# Constructing homogeneous sums with exactly the requested parities

The specified Pi structure supplies a shift for each requested degree.
Finite biproducts and the existing homogeneous matrix-unit construction
then give the object and both matrix maps. Choice acts on the whole data
record, and its laws verify that exact record.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusion.{0, 0}) (S : C.data.Obj) {n : ℕ} (a : Fin n → ZMod 2)

theorem exists_homogeneousRealizationData :
    ∃ d : HomogeneousRealizationData C.data.toWeaklyPointedSuperfusionData S n,
      HomogeneousRealizationLaws C.data.toWeaklyPointedSuperfusionData a d := by
  classical
  choose T hT using fun i => exists_homogeneous_shift C S (a i)
  obtain ⟨Y, hY⟩ := C.laws.has_finite_biproducts T
  obtain ⟨d, hd, ha⟩ := exists_homogeneousSum_of_degrees C.laws.toWeaklyPointedSuperfusionLaws a hT hY
  exact ⟨⟨Y, d⟩, ⟨hd, ha⟩⟩

noncomputable def homogeneousRealizationData :
    HomogeneousRealizationData C.data.toWeaklyPointedSuperfusionData S n :=
  (exists_homogeneousRealizationData C S a).choose

theorem homogeneousRealizationLaws :
    HomogeneousRealizationLaws C.data.toWeaklyPointedSuperfusionData a
      (homogeneousRealizationData C S a) :=
  (exists_homogeneousRealizationData C S a).choose_spec

noncomputable def homogeneousRealization : HomogeneousRealization C.toWeaklyPointedSuperfusion S a :=
  ⟨homogeneousRealizationData C S a, homogeneousRealizationLaws C S a⟩

def HomogeneousRealization.toHomogeneousSum {D : WeaklyPointedSuperfusion.{0, 0}}
    {T : D.data.Obj} {m : ℕ} {b : Fin m → ZMod 2} (d : HomogeneousRealization D T b) :
    HomogeneousSum D.data T d.data.object m := ⟨d.data.presentation, d.laws.presentation⟩

end RMod.Classification
