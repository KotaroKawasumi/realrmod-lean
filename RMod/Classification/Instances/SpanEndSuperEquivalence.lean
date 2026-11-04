import RMod.Classification.Instances.SpanEndFunctors
import RMod.Classification.Instances.EndGrading
import Superfusion.Category.EndSuperAlgebra
import Superfusion.Super.GradedTransfer
import Superfusion.Super.BWPeriodicity

/-!
# The graded endomorphism equivalence of a fully faithful span functor

The underlying algebra map is exactly the given functor map. Its grading
law and full faithfulness upgrade it to the existing superalgebra
equivalence interface, so tensor congruence acts on the specified maps.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanSuperfunctor

open CategoryTheory Superfusion

attribute [local implicit_reducible] CategoryTheory.End
  Superfusion.Category.endSuperAlgebra Superfusion.Category.endGrading

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

noncomputable def endSuperEquiv (F : SpanSuperfunctor C D S T)
    (hF : F.toFunctor.FullyFaithful) (X : HomogeneousSpanCategory C S) :
    SuperAlgEquiv (Superfusion.Category.endSuperAlgebra (K := ℝ) (C := LinearCategory C) X.obj)
      (Superfusion.Category.endSuperAlgebra (K := ℝ) (C := LinearCategory D) (F.data.obj X).obj) where
  toAlgEquiv := F.endAlgEquiv hF X
  map_grading i := map_grading_of_bijective
    (Superfusion.Category.endGrading (K := ℝ) (C := LinearCategory C) X.obj)
    (Superfusion.Category.endGrading (K := ℝ) (C := LinearCategory D) (F.data.obj X).obj)
    (F.endAlgHom X)
    (fun _ f hf => F.laws.map_grade (ObjectProperty.homMk f : X ⟶ X) hf)
    (F.endAlgHom_bijective hF X) i

end RMod.Classification.SpanSuperfunctor
