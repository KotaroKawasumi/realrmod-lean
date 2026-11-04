import RMod.Classification.Instances.SpanGenerator
import RMod.Classification.Proofs.SpanSimpleImages
import RMod.Classification.Proofs.SpanSuperequivalence
import RMod.Classification.Proofs.HomogeneousSpanMembership

/-!
# Detecting the target component from a generator retract

A component equivalence sends its simple generator to a simple object.
If that image is a homogeneous retract of an object in another simple
span, the two target generators lie in the same parity orbit.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

theorem span_target_orbit_of_retract {C D : WeaklyPointedSuperfusion.{0, 0}}
    {S : C.data.Obj} {T W : D.data.Obj}
    (hS : C.data.IsSimple S) (hT : D.data.IsSimple T) (hW : D.data.IsSimple W)
    (E : SpanSuperequivalence C D S T) (X : HomogeneousSpanCategory C S)
    (i : spanGenerator C S ⟶ X) (p : X ⟶ spanGenerator C S)
    (hip : i ≫ p = 𝟙 _) {a : ZMod 2} (hi : C.data.IsHomogeneous a i.hom)
    (hX : InHomogeneousSpan D W (E.forwardFunctor.data.obj X).obj) :
    SameParityOrbit D.data T W := by
  let Y := E.forwardFunctor.data.obj (spanGenerator C S)
  have hY := E.forwardFunctor.map_simple E.fullyFaithful E.map_grade_iff
    (spanGenerator C S) hS
  have hcomp : E.forwardFunctor.data.map i ≫ E.forwardFunctor.data.map p = 𝟙 _ :=
    (E.forwardFunctor.laws.map_comp i p).symm.trans
      ((congrArg E.forwardFunctor.data.map hip).trans (E.forwardFunctor.laws.map_id _))
  have hYW : InHomogeneousSpan D W Y.obj := inHomogeneousSpan_of_retract D hW hX
    (E.forwardFunctor.data.map i).hom (E.forwardFunctor.data.map p).hom
    (congrArg (fun f : Y ⟶ Y => f.hom) hcomp) (E.forwardFunctor.laws.map_grade i hi)
  exact SameParityOrbit.trans D.laws (sameParityOrbit_of_simple_in_span D T Y hT hY).symm
    (sameParityOrbit_of_simple_in_span D W ⟨Y.obj, hYW⟩ hW hY)

end RMod.Classification
