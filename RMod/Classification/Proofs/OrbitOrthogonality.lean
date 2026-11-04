import RMod.Classification.Proofs.Grading

/-!
# Orthogonality of distinct homogeneous simple orbits

Graded Schur kills each homogeneous component of a morphism between
simples in distinct parity orbits. The direct-sum grading then kills the
whole Hom space. This uses no reference type or property P.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem hom_zero_of_not_sameParityOrbit (C : WeaklyPointedSuperfusion.{0, 0})
    {X Y : C.data.Obj} (hX : C.data.IsSimple X) (hY : C.data.IsSimple Y)
    (h : ¬ SameParityOrbit C.data X Y) (f : C.data.Hom X Y) : f = C.data.zero := by
  have hh {a : ZMod 2} (g : C.data.Hom X Y) (hg : C.data.IsHomogeneous a g) : g = C.data.zero := by
    by_contra hne
    exact h ⟨a, homogeneous_schur C.laws hX hY g hg hne⟩
  obtain ⟨f₀, f₁, h₀, h₁, hf⟩ := C.laws.grade_decomposition f
  rw [← hf, hh f₀ h₀, hh f₁ h₁, C.laws.zero_add]

end RMod.Classification
