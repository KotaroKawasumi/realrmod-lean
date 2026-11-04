import RMod.Classification.Abstract.Pi

/-!
# Auxiliary finite sum choices for the implementation

Objects, inclusions and projections are data; the biproduct identities are
laws on those data. These choices are constructed on the proof side and
are not part of the Challenge statement.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0})

structure BiproductData {n : ℕ} (S : Fin n → C.Obj) where
  object : C.Obj
  inclusion : (i : Fin n) → C.Hom (S i) object
  projection : (i : Fin n) → C.Hom object (S i)

structure BiproductLaws {n : ℕ} (S : Fin n → C.Obj) (d : BiproductData C S) : Prop where
  inclusion_even : ∀ i, C.IsHomogeneous 0 (d.inclusion i)
  projection_even : ∀ i, C.IsHomogeneous 0 (d.projection i)
  diagonal : ∀ i, C.comp (d.inclusion i) (d.projection i) = C.id (S i)
  off_diagonal : ∀ i j, i ≠ j → C.comp (d.inclusion i) (d.projection j) = C.zero
  total : C.finSum n (fun i => C.comp (d.projection i) (d.inclusion i)) = C.id d.object

structure Biproduct {n : ℕ} (S : Fin n → C.Obj) where
  data : BiproductData C S
  laws : BiproductLaws C S data

structure FiniteSumsData where
  sum : {n : ℕ} → (S : Fin n → C.Obj) → BiproductData C S

structure FiniteSumsLaws (d : FiniteSumsData C) : Prop where
  sum : ∀ {n : ℕ} (S : Fin n → C.Obj), BiproductLaws C S (d.sum S)

structure FiniteSums where
  data : FiniteSumsData C
  laws : FiniteSumsLaws C data

end RMod.Classification
