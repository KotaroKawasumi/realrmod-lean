import RMod.Classification.Instances.UnitTensorComparison
import RMod.Classification.Instances.SimpleOrbits
import RMod.Classification.Proofs.UnitComparisonCoherence

/-!
# The two canonical tensor comparisons coincide at the unit pair

The source unitors agree by monoidal coherence. In the target, both
insertions of the specified even unit isomorphism agree. Composing these
equalities proves exact equality of the two comparison maps, rather than
equality only up to a real scalar.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {U : C.data.Obj}

theorem unitTensorComparisons_equal
    (E : SpanSuperfunctor A C A.data.tensorUnit U)
    {i : IsoData C.data C.data.tensorUnit (E.data.obj (spanGenerator A A.data.tensorUnit)).obj}
    (hi : EvenIsoLaws C.data i) :
    (leftUnitTensorComparisonData (unitSimple A) E.data E.data i).hom =
      (rightUnitTensorComparisonData (unitSimple A) E.data E.data i).hom := by
  let X := leftUnitSpanObject A (unitSimple A)
  let Y := spanGenerator A A.data.tensorUnit
  have hm : (E.data.map (ObjectProperty.homMk (A.data.leftUnitorHom A.data.tensorUnit) : X ⟶ Y)).hom =
      (E.data.map (ObjectProperty.homMk (A.data.rightUnitorHom A.data.tensorUnit) : X ⟶ Y)).hom :=
    congrArg (fun f : X ⟶ Y => (E.data.map f).hom)
      (ObjectProperty.hom_ext _ (unitors_hom_equal A.laws))
  let l : C.data.Hom (E.data.obj X).obj (E.data.obj Y).obj :=
    (E.data.map (ObjectProperty.homMk (A.data.leftUnitorHom A.data.tensorUnit) : X ⟶ Y)).hom
  let r : C.data.Hom (E.data.obj X).obj (E.data.obj Y).obj :=
    (E.data.map (ObjectProperty.homMk (A.data.rightUnitorHom A.data.tensorUnit) : X ⟶ Y)).hom
  change l = r at hm
  change C.data.comp (C.data.comp l (C.data.leftUnitorInv (E.data.obj Y).obj))
      (C.data.tensorHom i.hom (C.data.id (E.data.obj Y).obj)) =
    C.data.comp (C.data.comp r (C.data.rightUnitorInv (E.data.obj Y).obj))
      (C.data.tensorHom (C.data.id (E.data.obj Y).obj) i.hom)
  rw [hm, C.laws.comp_assoc, C.laws.comp_assoc, unit_insertions_equal C.laws hi]

end RMod.Classification
