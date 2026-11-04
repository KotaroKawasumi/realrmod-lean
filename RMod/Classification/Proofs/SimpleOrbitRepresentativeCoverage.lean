import RMod.Classification.Instances.SimpleOrbitRepresentatives

/-!
# The intrinsic representatives give distinct and exhaustive components

Their quotient classes are their indices. Equality or existence of a
parity-orbit comparison therefore follows directly from the quotient,
without making any additional choice of representative or type label.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem simpleOrbitRepresentatives_separate (g h : SimpleOrbit C) (hgh : g ≠ h) :
    ¬ SameParityOrbit C.data (simpleOrbitRepresentative C g).data.object
      (simpleOrbitRepresentative C h).data.object := by
  intro he
  apply hgh
  have hh := @Quotient.sound (SimpleObject C) (simpleOrbitSetoid C)
    (simpleOrbitRepresentative C g) (simpleOrbitRepresentative C h) he
  exact (simpleOrbitRepresentative_class C g).symm.trans (hh.trans (simpleOrbitRepresentative_class C h))

theorem simpleOrbitRepresentatives_cover (T : C.data.Obj) (hT : C.data.IsSimple T) :
    ∃ g : SimpleOrbit C, SameParityOrbit C.data (simpleOrbitRepresentative C g).data.object T := by
  let t : SimpleObject C := ⟨⟨T⟩, ⟨hT⟩⟩
  refine ⟨simpleOrbitMk C t, ?_⟩
  exact @Quotient.exact (SimpleObject C) (simpleOrbitSetoid C)
    (simpleOrbitRepresentative C (simpleOrbitMk C t)) t (simpleOrbitRepresentative_class C (simpleOrbitMk C t))

end RMod.Classification
