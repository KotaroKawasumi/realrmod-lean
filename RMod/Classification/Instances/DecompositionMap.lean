import RMod.Classification.Abstract.Decomposition
import RMod.Classification.Proofs.Functors

/-!
# Mapping a chosen finite decomposition

A superfunctor maps the supplied inclusion and projection data. Its
linear functor laws prove all matrix identities and completeness on the
full Hom spaces. Keeping the maps explicit lets tensor functors transport
summand tests for equality without introducing any new sum choices.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.Decomposition

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}} {D : WeaklyPointedSuperfusion.{u₂, v₂}}
  {X : C.data.Obj} {n : ℕ} {S : Fin n → C.data.Obj}

def mapData (F : SuperfunctorData C.data D.data) (d : DecompositionData C.data X S) :
    DecompositionData D.data (F.obj X) (fun i => F.obj (S i)) where
  inclusion i := F.map (d.inclusion i)
  projection i := F.map (d.projection i)

theorem mapLaws (F : Superfunctor C D) (d : Decomposition C X S) :
    DecompositionLaws (mapData F.data d.data) where
  inclusion_even i := F.laws.map_grade _ (d.laws.inclusion_even i)
  projection_even i := F.laws.map_grade _ (d.laws.projection_even i)
  diagonal i := by
    change D.data.comp (F.data.map (d.data.inclusion i)) (F.data.map (d.data.projection i)) = _
    rw [← F.laws.map_comp, d.laws.diagonal, F.laws.map_id]
  off_diagonal i j hij := by
    change D.data.comp (F.data.map (d.data.inclusion i)) (F.data.map (d.data.projection j)) = _
    rw [← F.laws.map_comp, d.laws.off_diagonal i j hij, F.laws.map_zero]
  total := by
    change D.data.finSum n (fun i => D.data.comp
      (F.data.map (d.data.projection i)) (F.data.map (d.data.inclusion i))) = _
    simp only [← F.laws.map_comp]
    rw [← F.map_finSum, d.laws.total, F.laws.map_id]

def map (F : Superfunctor C D) (d : Decomposition C X S) :
    Decomposition D (F.data.obj X) (fun i => F.data.obj (S i)) :=
  ⟨mapData F.data d.data, mapLaws F d⟩

end RMod.Classification.Decomposition
