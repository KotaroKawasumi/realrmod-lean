import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Proofs.Functors

/-!
# A superfunctor maps specified homogeneous sums and their spans

Keep each summand's parity and apply the specified map to its inclusion
and projection. The functor's linearity and composition laws prove the
matrix-unit identities for these exact data. This supplies component
membership when restricting an arbitrary equivalence to its simple orbits.
-/

set_option autoImplicit false

namespace RMod.Classification.Superfunctor

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (F : Superfunctor C D)
  {X Y : C.data.Obj} {n : ℕ}

def mapHomogeneousSumData (d : HomogeneousSumData C.data X Y n) :
    HomogeneousSumData D.data (F.data.obj X) (F.data.obj Y) n where
  parity := d.parity
  inclusion i := F.data.map (d.inclusion i)
  projection i := F.data.map (d.projection i)

theorem mapHomogeneousSumLaws {d : HomogeneousSumData C.data X Y n} (hd : HomogeneousSumLaws d) :
    HomogeneousSumLaws (F.mapHomogeneousSumData d) where
  inclusion_grade i := F.laws.map_grade _ (hd.inclusion_grade i)
  projection_grade i := F.laws.map_grade _ (hd.projection_grade i)
  diagonal i := (F.laws.map_comp _ _).symm.trans
    ((congrArg F.data.map (hd.diagonal i)).trans (F.laws.map_id X))
  off_diagonal i j hij := (F.laws.map_comp _ _).symm.trans
    ((congrArg F.data.map (hd.off_diagonal i j hij)).trans (F.laws.map_zero X X))
  total := by
    change D.data.finSum n (fun i => D.data.comp (F.data.map (d.projection i))
      (F.data.map (d.inclusion i))) = D.data.id (F.data.obj Y)
    simp only [← F.laws.map_comp]
    rw [← F.map_finSum, hd.total, F.laws.map_id]

def mapHomogeneousSum (d : HomogeneousSum C.data X Y n) :
    HomogeneousSum D.data (F.data.obj X) (F.data.obj Y) n :=
  ⟨F.mapHomogeneousSumData d.data, F.mapHomogeneousSumLaws d.laws⟩

theorem map_homogeneousSpan {S : C.data.Obj} (h : InHomogeneousSpan C S X) :
    InHomogeneousSpan D (F.data.obj S) (F.data.obj X) := by
  obtain ⟨m, ⟨d⟩⟩ := h
  exact ⟨m, ⟨F.mapHomogeneousSum d⟩⟩

end RMod.Classification.Superfunctor
