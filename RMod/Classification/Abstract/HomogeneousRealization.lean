import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Abstract.Pi

/-!
# Realizing a prescribed finite list of homogeneous copies

The resulting object and all inclusions and projections are data.
Their matrix identities and their prescribed parity list are laws on
those data. This construction does not require the generator to be simple.
-/

set_option autoImplicit false

namespace RMod.Classification

structure HomogeneousRealizationData (C : WeaklyPointedSuperfusionData.{0, 0})
    (S : C.Obj) (n : ℕ) where
  object : C.Obj
  presentation : HomogeneousSumData C S object n

structure HomogeneousRealizationLaws (C : WeaklyPointedSuperfusionData.{0, 0})
    {S : C.Obj} {n : ℕ} (a : Fin n → ZMod 2) (d : HomogeneousRealizationData C S n) : Prop where
  presentation : HomogeneousSumLaws d.presentation
  parity : d.presentation.parity = a

structure HomogeneousRealization (C : WeaklyPointedSuperfusion.{0, 0})
    (S : C.data.Obj) {n : ℕ} (a : Fin n → ZMod 2) where
  data : HomogeneousRealizationData C.data S n
  laws : HomogeneousRealizationLaws C.data a data

end RMod.Classification
