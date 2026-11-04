import RMod.Classification.Instances.SimpleOrbitGroup

/-!
# Simple representatives normalized at the identity class

Choose a representative of each intrinsic parity orbit using Mathlib's
quotient representative. At the identity class choose the specified
tensor unit itself. Object data are chosen first; simplicity and the
class equation are proved for exactly those choices.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

noncomputable def simpleOrbitRepresentativeData (g : SimpleOrbit C) : SimpleObjectData C.data := by
  classical
  exact if g = 1 then unitSimpleData C else (Quotient.out g).data

theorem simpleOrbitRepresentativeLaws (g : SimpleOrbit C) :
    SimpleObjectLaws C.data (simpleOrbitRepresentativeData C g) := by
  classical
  by_cases h : g = 1
  · simpa only [simpleOrbitRepresentativeData, if_pos h] using unitSimpleLaws C
  · simpa only [simpleOrbitRepresentativeData, if_neg h] using (Quotient.out g).laws

noncomputable def simpleOrbitRepresentative (g : SimpleOrbit C) : SimpleObject C :=
  ⟨simpleOrbitRepresentativeData C g, simpleOrbitRepresentativeLaws C g⟩

theorem simpleOrbitRepresentative_one : simpleOrbitRepresentative C 1 = unitSimple C := by
  classical
  simp only [simpleOrbitRepresentative, simpleOrbitRepresentativeData]
  rfl

theorem simpleOrbitRepresentative_class (g : SimpleOrbit C) :
    simpleOrbitMk C (simpleOrbitRepresentative C g) = g := by
  classical
  by_cases h : g = 1
  · subst g
    rw [simpleOrbitRepresentative_one]
    rfl
  · have he : simpleOrbitRepresentative C g = Quotient.out g := by
      simp only [simpleOrbitRepresentative, simpleOrbitRepresentativeData, if_neg h]
    rw [he]
    exact Quotient.out_eq g

end RMod.Classification
