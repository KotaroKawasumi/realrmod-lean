import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Proofs.Decompositions
import RMod.Classification.Proofs.OrbitOrthogonality

/-!
# Orthogonality of entire simple-orbit components

Homogeneous inclusions and projections detect every morphism between
their spans. Each resulting generator-to-generator entry vanishes by
graded Schur when the simple generators have distinct parity orbits.
-/

set_option autoImplicit false

namespace RMod.Classification

theorem hom_zero_of_distinct_spans (C : WeaklyPointedSuperfusion.{0, 0})
    {S T X Y : C.data.Obj} (hS : C.data.IsSimple S) (hT : C.data.IsSimple T)
    (hST : ¬ SameParityOrbit C.data S T)
    (hX : InHomogeneousSpan C S X) (hY : InHomogeneousSpan C T Y)
    (f : C.data.Hom X Y) : f = C.data.zero := by
  obtain ⟨n, ⟨d⟩⟩ := hX
  obtain ⟨m, ⟨e⟩⟩ := hY
  apply hom_ext_of_inclusions C.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  apply hom_ext_of_projections C.laws e.data.inclusion e.data.projection e.laws.total
  intro j
  have hh := hom_zero_of_not_sameParityOrbit C hS hT hST
    (C.data.comp (C.data.comp (d.data.inclusion i) f) (e.data.projection j))
  rw [hh, raw_comp_zero C.laws, raw_zero_comp C.laws]

end RMod.Classification
