import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Chosen finite decomposition maps

The inclusions and projections of a finite decomposition are retained as
data. Their parity and matrix-unit identities are laws on those maps.
This proof-side presentation is for repeated coordinate calculations;
the public HasDecomposition predicate remains unchanged.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

structure DecompositionData (C : WeaklyPointedSuperfusionData.{u, v})
    (X : C.Obj) {n : ℕ} (S : Fin n → C.Obj) where
  inclusion : (i : Fin n) → C.Hom (S i) X
  projection : (i : Fin n) → C.Hom X (S i)

structure DecompositionLaws {C : WeaklyPointedSuperfusionData.{u, v}}
    {X : C.Obj} {n : ℕ} {S : Fin n → C.Obj} (d : DecompositionData C X S) : Prop where
  inclusion_even : ∀ i, C.IsHomogeneous 0 (d.inclusion i)
  projection_even : ∀ i, C.IsHomogeneous 0 (d.projection i)
  diagonal : ∀ i, C.comp (d.inclusion i) (d.projection i) = C.id (S i)
  off_diagonal : ∀ i j, i ≠ j → C.comp (d.inclusion i) (d.projection j) = C.zero
  total : C.finSum n (fun i => C.comp (d.projection i) (d.inclusion i)) = C.id X

structure Decomposition (C : WeaklyPointedSuperfusion.{u, v})
    (X : C.data.Obj) {n : ℕ} (S : Fin n → C.data.Obj) where
  data : DecompositionData C.data X S
  laws : DecompositionLaws data

end RMod.Classification
