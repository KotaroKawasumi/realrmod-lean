import RMod.Classification.Abstract.SpanSuperequivalence
import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Instances.SpanGenerator

/-!
# A group-indexed system of component equivalences

The data retain actual functors, inverses, and the unit comparison.
Their superlinear and evenness laws are asserted separately. The two
families of generators are required to use the actual units at one.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : WeaklyPointedSuperfusion.{0, 0}) (G : Type) [Group G]
  (S : G → A.data.Obj) (T : G → C.data.Obj)

structure ComponentSystemData where
  component : ∀ g, SpanSuperequivalenceData A C (S g) (T g)
  unitIso : IsoData C.data C.data.tensorUnit
    ((component 1).functor.obj (spanGenerator A (S 1))).obj

structure ComponentSystemLaws (d : ComponentSystemData A C G S T) : Prop where
  component : ∀ g, SpanSuperequivalenceLaws A C (S g) (T g) (d.component g)
  source_unit : S 1 = A.data.tensorUnit
  target_unit : T 1 = C.data.tensorUnit
  unit_even : EvenIsoLaws C.data d.unitIso

structure ComponentSystem where
  data : ComponentSystemData A C G S T
  laws : ComponentSystemLaws A C G S T data

end RMod.Classification
