import RMod.Classification.Proofs.IsoEqualityMaps

/-!
# Equality of indices is natural for an indexed family of raw morphisms

The chosen source and target equality proofs have no computational
content. After equality elimination the square is exactly the two
identity composition laws of the supplied category.
-/

set_option autoImplicit false
universe w

namespace RMod.Classification

theorem indexed_morphism_eq_naturality (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type w} (P Q : I → C.data.Obj) (f : ∀ i, C.data.Hom (P i) (Q i))
    {i j : I} (e : i = j) (eP : P i = P j) (eQ : Q i = Q j) :
    C.data.comp (f i) (IsoData.ofEq C.data eQ).hom =
      C.data.comp (IsoData.ofEq C.data eP).hom (f j) := by
  cases e
  change C.data.comp (f i) (C.data.id _) = C.data.comp (C.data.id _) (f i)
  rw [C.laws.comp_id, C.laws.id_comp]

end RMod.Classification
