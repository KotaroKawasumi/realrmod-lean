import RMod.Classification.Proofs.DualAdjunctionGrading

/-!
# Explicit real-linear dual Hom equivalences

Both maps and inverses are those of the proved full adjunctions. These
equivalences are on complete real Hom spaces, with exact parity control,
so they can be used for dimensions and representation of functionals.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{u, v}} {X Y : C.data.Obj} (p : DualPairing C X Y)

def rightHomLinearEquiv (U V : LinearCategory C) :
    ((tensorRightFunctor C X).obj U ⟶ V) ≃ₗ[ℝ] (U ⟶ (tensorRightFunctor C Y).obj V) :=
  (tensorRightSuperfunctor C X).homLinearEquiv (tensorRightSuperfunctor C Y) p.rightAdjunction U V

def leftHomLinearEquiv (U V : LinearCategory C) :
    ((tensorLeftFunctor C Y).obj U ⟶ V) ≃ₗ[ℝ] (U ⟶ (tensorLeftFunctor C X).obj V) :=
  (tensorLeftSuperfunctor C Y).homLinearEquiv (tensorLeftSuperfunctor C X) p.leftAdjunction U V

theorem rightHomLinearEquiv_grade_iff (U V : LinearCategory C) {a : ZMod 2}
    (f : (tensorRightFunctor C X).obj U ⟶ V) :
    C.data.IsHomogeneous a (p.rightHomLinearEquiv U V f) ↔ C.data.IsHomogeneous a f :=
  (tensorRightSuperfunctor C X).homEquiv_grade_iff (tensorRightSuperfunctor C Y) p.rightAdjunction
    p.rightAdjunction_unit_even p.rightAdjunction_counit_even f

theorem leftHomLinearEquiv_grade_iff (U V : LinearCategory C) {a : ZMod 2}
    (f : (tensorLeftFunctor C Y).obj U ⟶ V) :
    C.data.IsHomogeneous a (p.leftHomLinearEquiv U V f) ↔ C.data.IsHomogeneous a f :=
  (tensorLeftSuperfunctor C Y).homEquiv_grade_iff (tensorLeftSuperfunctor C X) p.leftAdjunction
    p.leftAdjunction_unit_even p.leftAdjunction_counit_even f

end RMod.Classification.DualPairing
