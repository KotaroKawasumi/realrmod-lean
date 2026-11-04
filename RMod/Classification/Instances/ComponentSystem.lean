import RMod.Classification.Abstract.ComponentSystem
import RMod.Classification.Instances.SpanSuperequivalence

/-! # Completed component equivalences retained by a component system -/

set_option autoImplicit false

namespace RMod.Classification.ComponentSystem

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {G : Type} [Group G]
  {S : G → A.data.Obj} {T : G → C.data.Obj}

def component (d : ComponentSystem A C G S T) (g : G) : SpanSuperequivalence A C (S g) (T g) :=
  ⟨d.data.component g, d.laws.component g⟩

end RMod.Classification.ComponentSystem
