import RMod.Classification.Instances.AdjunctionFromEven

/-!
# The real-linear Hom equivalence of an adjunction

The forward Hom map is composition with the unit after the inverse functor
map. Linearity is therefore supplied by Mathlib preadditivity and the
existing functor linearity. The inverse remains Mathlib's explicit counit
formula.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.Superfunctor

attribute [local implicit_reducible] toFunctor

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

def homLinearEquiv (F : Superfunctor C D) (G : Superfunctor D C)
    (adj : F.toFunctor ⊣ G.toFunctor) (X : LinearCategory C) (Y : LinearCategory D) :
    (F.toFunctor.obj X ⟶ Y) ≃ₗ[ℝ] (X ⟶ G.toFunctor.obj Y) :=
  { adj.homEquiv X Y with
    map_add' f g := by
      change C.data.comp (adj.unit.app X) (G.data.map (D.data.add f g)) =
        C.data.add (C.data.comp (adj.unit.app X) (G.data.map f))
          (C.data.comp (adj.unit.app X) (G.data.map g))
      rw [G.laws.map_add]
      exact C.laws.comp_add _ _ _
    map_smul' r f := by
      change C.data.comp (adj.unit.app X) (G.data.map (D.data.smul r f)) =
        C.data.smul r (C.data.comp (adj.unit.app X) (G.data.map f))
      rw [G.laws.map_smul]
      exact C.laws.comp_smul r _ _ }

end RMod.Classification.Superfunctor
