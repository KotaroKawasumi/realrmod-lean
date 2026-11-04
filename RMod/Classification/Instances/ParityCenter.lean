import RMod.Classification.Proofs.ParityContractionCentral
import RMod.Classification.Instances.EvenIsos
import Mathlib.CategoryTheory.Monoidal.Center

/-!
# The specified parity object in Mathlib's Drinfeld center

The previously proved central comparison supplies the actual half-braiding
of the even category. Mathlib then provides its braided monoidal center and
the forgetful monoidal functor. This adapter retains the original maps;
it does not assume any additional coherence of the parity object.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

noncomputable def parityHalfBraiding : HalfBraiding (evenObj ℝ (LinearCategory C) p.object) where
  β X := IsoData.toEvenIso C ⟨p.centralHom X.obj, p.centralInv X.obj⟩
    ⟨hp.central_iso C.laws X.obj, hp.central_hom_even C.laws X.obj,
      hp.central_inv_even C.laws X.obj⟩
  naturality {X Y} f := by
    apply WideSubcategory.hom_ext
    exact hp.central_naturality C.laws f.hom
  monoidal X Y := by
    apply WideSubcategory.hom_ext
    change p.centralHom (C.data.tensorObj X.obj Y.obj) =
      C.data.comp (C.data.associatorInv p.object X.obj Y.obj)
        (C.data.comp (C.data.tensorHom (p.centralHom X.obj) (C.data.id Y.obj))
          (C.data.comp (C.data.associatorHom X.obj p.object Y.obj)
            (C.data.comp (C.data.tensorHom (C.data.id X.obj) (p.centralHom Y.obj))
              (C.data.associatorInv X.obj Y.obj p.object))))
    have he := hp.central_tensor C.laws X.obj Y.obj
    have hh := congrArg (fun f => C.data.comp (C.data.associatorInv p.object X.obj Y.obj)
      (C.data.comp f (C.data.associatorInv X.obj Y.obj p.object))) he
    simpa only [C.laws.comp_assoc, C.laws.associator_hom_inv, C.laws.comp_id,
      ← C.laws.comp_assoc (C.data.associatorInv p.object X.obj Y.obj)
        (C.data.associatorHom p.object X.obj Y.obj), C.laws.associator_inv_hom,
      C.laws.id_comp] using hh

noncomputable def parityCenter : Center (EvenSubcategory ℝ (LinearCategory C)) :=
  ⟨evenObj ℝ (LinearCategory C) p.object, parityHalfBraiding C p hp⟩

end RMod.Classification
