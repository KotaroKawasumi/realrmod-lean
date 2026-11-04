import RMod.Classification.Abstract.HomogeneousSums
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensoring the data of homogeneous sum presentations

Pairs of summands are indexed using Mathlib's finite-product equivalence.
Their inclusions are tensors of inclusions. Their projections include
the Koszul sign needed to cancel the crossing in their inverse identity.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomogeneousSum

variable {C : WeaklyPointedSuperfusionData.{u, v}} {S T X Y : C.Obj} {n m : ℕ}

def tensorData (d : HomogeneousSumData C S X n) (e : HomogeneousSumData C T Y m) :
    HomogeneousSumData C (C.tensorObj S T) (C.tensorObj X Y) (n * m) where
  parity k := d.parity (finProdFinEquiv.symm k).1 + e.parity (finProdFinEquiv.symm k).2
  inclusion k := C.tensorHom (d.inclusion (finProdFinEquiv.symm k).1)
    (e.inclusion (finProdFinEquiv.symm k).2)
  projection k := C.smul
    ((-1 : ℝ) ^ (e.parity (finProdFinEquiv.symm k).2 * d.parity (finProdFinEquiv.symm k).1).val)
    (C.tensorHom (d.projection (finProdFinEquiv.symm k).1) (e.projection (finProdFinEquiv.symm k).2))

end RMod.Classification.HomogeneousSum
