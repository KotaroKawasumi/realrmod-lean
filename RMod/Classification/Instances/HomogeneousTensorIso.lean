import RMod.Classification.Abstract.HomogeneousIso

/-!
# Tensoring specified homogeneous inverse pairs

Both maps are fixed explicitly. The inverse has the Koszul sign required
when the two inverse factors cross. For even structural maps this sign
is one; keeping it here also covers odd component comparisons.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.IsoData

variable (C : WeaklyPointedSuperfusionData.{u, v})

def homogeneousTensor {X X' Y Y' : C.Obj} (a b : ZMod 2)
    (d : IsoData C X X') (e : IsoData C Y Y') :
    IsoData C (C.tensorObj X Y) (C.tensorObj X' Y') :=
  ⟨C.tensorHom d.hom e.hom,
    C.smul ((-1 : ℝ) ^ (b * a).val) (C.tensorHom d.inv e.inv)⟩

end RMod.Classification.IsoData
