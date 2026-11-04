import RMod.Classification.Instances.LinearCategory
import Mathlib.CategoryTheory.Conj

/-!
# Linear conjugation of endomorphism algebras

Mathlib's conjugation equivalence is linear in a real linear category.
The algebra equivalence below keeps its specified forward and inverse
maps. No choice of endomorphism coordinates is involved.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

variable {C : Type*} [Category C] [Preadditive C] [Linear ℝ C] {X Y : C}

def endConjugation (e : X ≅ Y) : End X ≃ₐ[ℝ] End Y :=
  AlgEquiv.ofLinearEquiv
    { e.conj.toEquiv with
      map_add' := fun f g =>
        (congrArg (fun k : X ⟶ Y => e.inv ≫ k) (Preadditive.add_comp X X Y f g e.hom)).trans
          (Preadditive.comp_add Y X Y e.inv (f ≫ e.hom) (g ≫ e.hom))
      map_smul' := fun r f =>
        (congrArg (fun k : X ⟶ Y => e.inv ≫ k) (Linear.smul_comp X X Y r f e.hom)).trans
          (Linear.comp_smul Y X Y e.inv r (f ≫ e.hom)) }
    (map_one e.conj) (map_mul e.conj)

theorem endConjugation_apply (e : X ≅ Y) (f : End X) :
    endConjugation e f = e.inv ≫ f ≫ e.hom := rfl

end RMod.Classification
