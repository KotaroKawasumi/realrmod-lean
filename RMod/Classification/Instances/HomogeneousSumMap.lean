import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Proofs.Functors

/-!
# Mapping homogeneous sum presentations

A superfunctor maps the chosen inclusions and projections and retains their
parities. The matrix-unit equations follow from its composition and linear
laws. Tensoring by a fixed object is an important instance of this operation.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.HomogeneousSum

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}
  {X Y : C.data.Obj} {n : ℕ}

def mapData (F : SuperfunctorData C.data D.data) (d : HomogeneousSumData C.data X Y n) :
    HomogeneousSumData D.data (F.obj X) (F.obj Y) n where
  parity := d.parity
  inclusion i := F.map (d.inclusion i)
  projection i := F.map (d.projection i)

theorem mapLaws (F : Superfunctor C D) (d : HomogeneousSum C.data X Y n) :
    HomogeneousSumLaws (mapData F.data d.data) where
  inclusion_grade i := F.laws.map_grade _ (d.laws.inclusion_grade i)
  projection_grade i := F.laws.map_grade _ (d.laws.projection_grade i)
  diagonal i := by
    change D.data.comp (F.data.map (d.data.inclusion i)) (F.data.map (d.data.projection i)) = _
    rw [← F.laws.map_comp, d.laws.diagonal, F.laws.map_id]
  off_diagonal i j hij := by
    change D.data.comp (F.data.map (d.data.inclusion i)) (F.data.map (d.data.projection j)) = _
    rw [← F.laws.map_comp, d.laws.off_diagonal i j hij, F.laws.map_zero]
  total := by
    change D.data.finSum n (fun i =>
      D.data.comp (F.data.map (d.data.projection i)) (F.data.map (d.data.inclusion i))) = _
    simp only [← F.laws.map_comp]
    rw [← F.map_finSum, d.laws.total, F.laws.map_id]

def map (F : Superfunctor C D) (d : HomogeneousSum C.data X Y n) :
    HomogeneousSum D.data (F.data.obj X) (F.data.obj Y) n :=
  ⟨mapData F.data d.data, mapLaws F d⟩

end RMod.Classification.HomogeneousSum
