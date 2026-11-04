import RMod.Classification.Instances.ParityCenter

/-!
# The contraction as an isomorphism in the Drinfeld center

Compatibility with two central crossings is exactly the condition for the
specified contraction to be a morphism from pi tensor pi to the central
unit. Mathlib lifts its underlying even isomorphism to the center.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def parityContractionCenterHom :
    parityCenter C p hp ⊗ parityCenter C p hp ⟶ 𝟙_ (Center (EvenSubcategory ℝ (LinearCategory C))) where
  f := ⟨p.contractionHom, hp.contraction_hom_even C.laws⟩
  comm X := by
    apply WideSubcategory.hom_ext
    change C.data.comp (C.data.tensorHom p.contractionHom (C.data.id X.obj))
      (C.data.comp (C.data.leftUnitorHom X.obj) (C.data.rightUnitorInv X.obj)) =
      C.data.comp
        (C.data.comp (C.data.associatorHom p.object p.object X.obj)
          (C.data.comp (C.data.tensorHom (C.data.id p.object) (p.centralHom X.obj))
            (C.data.comp (C.data.associatorInv p.object X.obj p.object)
              (C.data.comp (C.data.tensorHom (p.centralHom X.obj) (C.data.id p.object))
                (C.data.associatorHom X.obj p.object p.object)))))
        (C.data.tensorHom (C.data.id X.obj) p.contractionHom)
    have he := congrArg (fun f => C.data.comp f (C.data.rightUnitorInv X.obj))
      (hp.contraction_central C.laws X.obj)
    simpa only [C.laws.comp_assoc, C.laws.right_unitor_hom_inv, C.laws.comp_id] using he

noncomputable def parityContractionCenterIso :
    parityCenter C p hp ⊗ parityCenter C p hp ≅ 𝟙_ (Center (EvenSubcategory ℝ (LinearCategory C))) := by
  let e := IsoData.toEvenIso C ⟨p.contractionHom, p.contractionInv⟩
    ⟨hp.contraction_iso C.laws, hp.contraction_hom_even C.laws, hp.contraction_inv_even C.laws⟩
  letI : IsIso (parityContractionCenterHom C p hp).f := e.isIso_hom
  exact Center.isoMk (parityContractionCenterHom C p hp)

end RMod.Classification
