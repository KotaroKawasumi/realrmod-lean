import RMod.Classification.Proofs.Functors

/-!
# Endomorphism algebra equivalences from fully faithful superfunctors

The linear map is Mathlib's map on Hom spaces. Bijectivity supplies its
inverse, and the identity and composition laws upgrade it to an algebra
equivalence. Categorical endomorphism multiplication reverses diagrammatic
composition, on both sides of this comparison.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification.Superfunctor

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{u₁, v₁}}
  {D : WeaklyPointedSuperfusion.{u₂, v₂}}

/-- The endomorphism algebra map uses only the given functor map. -/
def endAlgHom (F : Superfunctor C D) (X : LinearCategory C) :
    End X →ₐ[ℝ] End (C := LinearCategory D) (F.data.obj X) :=
  AlgHom.ofLinearMap (F.toFunctor.mapLinearMap ℝ)
    (F.laws.map_id X) (fun f g => F.laws.map_comp g f)

@[simp]
theorem endAlgHom_apply (F : Superfunctor C D) (X : LinearCategory C) (f : End X) :
    F.endAlgHom X f = F.data.map f := rfl

noncomputable def endAlgEquiv (F : Superfunctor C D) (X : LinearCategory C)
    (h : Function.Bijective (F.data.map : C.data.Hom X X → _)) :
    End X ≃ₐ[ℝ] End (C := LinearCategory D) (F.data.obj X) :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.ofBijective (F.toFunctor.mapLinearMap ℝ) h)
    (F.laws.map_id X) (fun f g => F.laws.map_comp g f)

@[simp]
theorem endAlgEquiv_apply (F : Superfunctor C D) (X : LinearCategory C)
    (h : Function.Bijective (F.data.map : C.data.Hom X X → _)) (f : End X) :
    F.endAlgEquiv X h f = F.data.map f := rfl

end RMod.Classification.Superfunctor
