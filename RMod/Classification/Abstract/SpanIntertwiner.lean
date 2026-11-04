import RMod.Classification.Abstract.SpanNatural
import RMod.Classification.Instances.SpanGenerator

/-!
# A homogeneous comparison at the generator

The single comparison morphism is data. Its degree and signed
intertwining equation against every generator endomorphism are laws.
Extending this datum to the span is a separate construction.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

structure SpanIntertwinerData (F G : SpanSuperfunctorData C D S T) where
  hom : F.obj (spanGenerator C S) ⟶ G.obj (spanGenerator C S)

structure SpanIntertwinerLaws {F G : SpanSuperfunctorData C D S T} (a : ZMod 2)
    (d : SpanIntertwinerData F G) : Prop where
  grade : D.data.IsHomogeneous a d.hom.hom
  intertwines : ∀ {b : ZMod 2} (f : spanGenerator C S ⟶ spanGenerator C S),
    C.data.IsHomogeneous b f.hom →
      F.map f ≫ d.hom = ((-1 : ℝ) ^ (a * b).val) • (d.hom ≫ G.map f)

structure SpanIntertwiner (F G : SpanSuperfunctor C D S T) (a : ZMod 2) where
  data : SpanIntertwinerData F.data G.data
  laws : SpanIntertwinerLaws a data

end RMod.Classification
