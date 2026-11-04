import RMod.Classification.Abstract.ParityOperations

/-!
# The right parity comparison

Tensoring the specified odd inverse pair on the right and applying the
right unitor gives the right-hand counterpart of z. Both directions are
explicit maps; their inverse and supernatural laws are proved separately.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

def rightZHom (X : C.Obj) : C.Hom (C.tensorObj X p.object) X :=
  C.comp (C.tensorHom (C.id X) p.hom) (C.rightUnitorHom X)

def rightZInv (X : C.Obj) : C.Hom X (C.tensorObj X p.object) :=
  C.comp (C.rightUnitorInv X) (C.tensorHom (C.id X) p.inv)

end RMod.Classification.PiData
