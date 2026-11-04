import RMod.Classification.Abstract.Pi

/-!
# Parity operations used by the construction and its proofs

These operations are internal to Solution. The Challenge leaves the entire
pullback/twist category as a definition hole rather than spelling out the
normalizers that construct its associator.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

namespace PiData

variable {C : WeaklyPointedSuperfusionData.{u, v}} (p : PiData C)

/-- Move the parity factor from the left to the right of `X`. -/
def centralHom (X : C.Obj) : C.Hom (C.tensorObj p.object X)
    (C.tensorObj X p.object) :=
  C.comp (C.comp (C.tensorHom p.hom (C.id X)) (C.leftUnitorHom X))
    (C.comp (C.rightUnitorInv X) (C.tensorHom (C.id X) p.inv))

/-- Reverse the central comparison, with no chosen inverse hidden in laws. -/
def centralInv (X : C.Obj) : C.Hom (C.tensorObj X p.object)
    (C.tensorObj p.object X) :=
  C.comp (C.tensorHom (C.id X) p.hom)
    (C.comp (C.rightUnitorHom X)
      (C.comp (C.leftUnitorInv X) (C.tensorHom p.inv (C.id X))))

/-- The minus sign is the manuscript's right-parity-factor normalization. -/
def contractionHom : C.Hom (C.tensorObj p.object p.object) C.tensorUnit :=
  C.neg (C.comp (C.tensorHom p.hom p.hom) (C.leftUnitorHom C.tensorUnit))

def contractionInv : C.Hom C.tensorUnit (C.tensorObj p.object p.object) :=
  C.comp (C.leftUnitorInv C.tensorUnit) (C.tensorHom p.inv p.inv)

/-- The two parity factors; zero is removed with actual unitors later. -/
def factor (a : ZMod 2) : C.Obj := if a = 0 then C.tensorUnit else p.object

end PiData
end RMod.Classification
