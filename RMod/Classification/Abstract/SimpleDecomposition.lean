import RMod.Classification.Abstract.Decomposition

/-!
# Chosen decompositions into simple objects

The finite family and its inclusion/projection maps are computational
data. Their simplicity and matrix identities are laws on those data.
This retains the witnesses needed when selecting tensor constituents.
-/

set_option autoImplicit false

namespace RMod.Classification

structure SimpleDecompositionData (C : WeaklyPointedSuperfusionData.{0, 0}) (X : C.Obj) where
  size : ℕ
  summand : Fin size → C.Obj
  decomposition : DecompositionData C X summand

structure SimpleDecompositionLaws (C : WeaklyPointedSuperfusionData.{0, 0}) {X : C.Obj}
    (d : SimpleDecompositionData C X) : Prop where
  simple : ∀ i, C.IsSimple (d.summand i)
  decomposition : DecompositionLaws d.decomposition

structure SimpleDecomposition (C : WeaklyPointedSuperfusion.{0, 0}) (X : C.data.Obj) where
  data : SimpleDecompositionData C.data X
  laws : SimpleDecompositionLaws C.data data

end RMod.Classification
