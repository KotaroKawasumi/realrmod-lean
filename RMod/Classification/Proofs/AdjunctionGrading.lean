import RMod.Classification.Instances.LinearAdjunction

/-!
# Grading of a linear adjunction

If unit and counit are even and both functors preserve grading, both Hom
maps preserve every homogeneous component. The inverse identities then
give exact reflection of parity as well as preservation.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.Superfunctor

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

theorem homEquiv_grade_iff (F : Superfunctor C D) (G : Superfunctor D C)
    (adj : F.toFunctor ⊣ G.toFunctor)
    (hη : ∀ X, C.data.IsHomogeneous 0 (adj.unit.app X))
    (hε : ∀ Y, D.data.IsHomogeneous 0 (adj.counit.app Y))
    {X : LinearCategory C} {Y : LinearCategory D} {a : ZMod 2} (f : F.toFunctor.obj X ⟶ Y) :
    C.data.IsHomogeneous a (adj.homEquiv X Y f) ↔ D.data.IsHomogeneous a f := by
  constructor
  · intro hf
    have h := D.laws.comp_grade _ _ (F.laws.map_grade _ hf) (hε Y)
    rw [add_zero] at h
    change D.data.IsHomogeneous a ((adj.homEquiv X Y).symm (adj.homEquiv X Y f)) at h
    rw [Equiv.symm_apply_apply] at h
    exact h
  · intro hf
    have h := C.laws.comp_grade _ _ (hη X) (G.laws.map_grade _ hf)
    rw [zero_add] at h
    exact h

end RMod.Classification.Superfunctor
