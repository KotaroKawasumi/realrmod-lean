import RMod.Classification.Instances.SimpleDecomposition
import RMod.Classification.Instances.Decomposition

/-!
# Nonempty simple decompositions and their original matrix presentation

The selected simple decomposition recovers the existing separated
decomposition interface. Its size is positive whenever the vertex is
nonzero, since an empty total matrix sum is the zero identity.
-/

set_option autoImplicit false

namespace RMod.Classification.SimpleDecomposition

variable {C : WeaklyPointedSuperfusion.{0, 0}} {X : C.data.Obj} (d : SimpleDecomposition C X)

def toDecomposition : Decomposition C X d.data.summand := ⟨d.data.decomposition, d.laws.decomposition⟩

theorem hasDecomposition : C.data.HasDecomposition X d.data.summand :=
  (hasDecomposition_iff C X d.data.summand).mpr ⟨d.toDecomposition⟩

theorem size_pos (hX : C.data.id X ≠ C.data.zero) : 0 < d.data.size := by
  rcases d with ⟨⟨n, S, m⟩, hl⟩
  change 0 < n
  by_contra hn
  have hz : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  exact hX hl.decomposition.total.symm

end RMod.Classification.SimpleDecomposition
