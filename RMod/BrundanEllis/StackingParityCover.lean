import RMod.Definitions.WeaklyPointedSuperfusion

/-! Objects decorated by an auxiliary parity. The morphism from (X,p) to
(Y,q) is the actual degree p+q component. The ordinary monoidal instances
are constructed separately, with all Koszul corrections explicit. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking

@[implicit_reducible]
def ParityCover (C : WeaklyPointedSuperfusion.{u, v}) : Type u := C.data.Obj × ZMod 2

namespace ParityCover

def Hom (C : WeaklyPointedSuperfusion.{u, v}) (X Y : ParityCover C) : Type v :=
  {f : C.data.Hom X.1 Y.1 // C.data.IsHomogeneous (X.2 + Y.2) f}

end ParityCover
end RMod.BrundanEllis.Stacking
