import RMod.Classification.Instances.SpanComparisonEquivalence
import RMod.Classification.Proofs.SimpleEndComparison

/-!
# Same-type simple generators have superlinearly equivalent components

The graded division classification supplies the actual generator algebra
isomorphism. Its entrywise action constructs a functor on every Hom
space, an inverse, and even natural unit and counit maps. Thus the result
is an equivalence of the homogeneous spans, not just equality of labels.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory Superfusion

theorem exists_componentComparison (C D : PiSuperfusion.{0, 0})
    (S : C.data.Obj) (T : D.data.Obj) (hS : C.data.IsSimple S) (hT : D.data.IsSimple T)
    {r : ZMod 8} (hr : HasBWType C.data.toWeaklyPointedSuperfusionData S r)
    (hs : HasBWType D.data.toWeaklyPointedSuperfusionData T r) :
    Nonempty (SpanSuperequivalence C.toWeaklyPointedSuperfusion D.toWeaklyPointedSuperfusion S T) := by
  obtain ⟨a⟩ := exists_simpleEndComparison C D S T hS hT hr hs
  apply Nonempty.intro
  apply spanComparisonSuperequivalence C D S T a.toAlgEquiv
  intro b f
  exact (mem_iff_map_mem _ _ a.toAlgEquiv a.map_grading).symm

end RMod.Classification
