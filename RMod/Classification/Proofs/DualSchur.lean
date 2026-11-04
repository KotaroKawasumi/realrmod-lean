import RMod.Classification.Proofs.DualMateCancellation
import RMod.Classification.Instances.Duals
import RMod.Classification.Proofs.EvenSimple
import RMod.Classification.Proofs.Grading

/-!
# The even Schur property passes to the opposite dual

An even nonzero endomorphism of the opposite dual has a nonzero mate on
the given simple. Graded Schur makes that mate invertible, and mate
cancellation reflects its inverse. This supplies the hypothesis of the
existing two-snake completion theorem without assuming rigidity of the
new convolution category.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v})

/-- The original graded Schur law, expressed in the ordinary even category. -/
theorem even_end_schur {X : C.data.Obj} (hX : C.data.IsSimple X)
    (f : evenObj ℝ (LinearCategory C) X ⟶ evenObj ℝ (LinearCategory C) X) (hf : f ≠ 0) :
    IsIso f := by
  have hne : f.hom ≠ C.data.zero := fun h => hf ((even_hom_eq_zero_iff C f).mp h)
  obtain ⟨g, hfg, hgf⟩ := C.laws.graded_schur hX hX f.hom f.property hne
  have hg := homogeneous_inverse C.laws f.hom g hfg hgf f.property
  exact ⟨⟨⟨g, hg⟩, WideSubcategory.hom_ext _ hfg, WideSubcategory.hom_ext _ hgf⟩⟩

namespace DualPairing

variable {C} {X Y : C.data.Obj} (q : DualPairing C X Y)

include q

/-- Even division of the right dual follows from simplicity of the left member. -/
theorem right_even_schur (hX : C.data.IsSimple X) (f : C.data.Hom Y Y)
    (hf : C.data.IsHomogeneous 0 f) (hne : f ≠ C.data.zero) : C.data.IsEvenIso f := by
  let X' := evenObj ℝ (LinearCategory C) X
  let Y' := evenObj ℝ (LinearCategory C) Y
  letI : CategoryTheory.HasLeftDual Y' := { leftDual := X', exact := q.toEvenPairing }
  let f' : Y' ⟶ Y' := ⟨f, hf⟩
  have hne' : f' ≠ 0 := fun h => hne (congrArg (fun k => k.hom) h)
  letI : IsIso (leftAdjointMate f') := even_end_schur C hX (leftAdjointMate f') (DualMate.left_mate_ne_zero hne')
  letI : IsIso f' := DualMate.left_mate_reflects_isIso f'
  exact (even_isIso_iff C f').mp inferInstance

/-- The left dual has the same property, using the right mate. -/
theorem left_even_schur (hY : C.data.IsSimple Y) (f : C.data.Hom X X)
    (hf : C.data.IsHomogeneous 0 f) (hne : f ≠ C.data.zero) : C.data.IsEvenIso f := by
  let X' := evenObj ℝ (LinearCategory C) X
  let Y' := evenObj ℝ (LinearCategory C) Y
  letI : CategoryTheory.HasRightDual X' := { rightDual := Y', exact := q.toEvenPairing }
  let f' : X' ⟶ X' := ⟨f, hf⟩
  have hne' : f' ≠ 0 := fun h => hne (congrArg (fun k => k.hom) h)
  letI : IsIso (rightAdjointMate f') := even_end_schur C hY (rightAdjointMate f') (DualMate.right_mate_ne_zero hne')
  letI : IsIso f' := DualMate.right_mate_reflects_isIso f'
  exact (even_isIso_iff C f').mp inferInstance

end DualPairing
end RMod.Classification
