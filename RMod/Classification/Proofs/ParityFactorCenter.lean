import RMod.Classification.Instances.ParityFactorCenter

/-!
# Identifying the center adapters with the raw parity operations

The center construction preserves the actual comparison and multiplication
maps. Forgetting the half-braiding and central-morphism equations therefore
gives coherence for both parity values with the specified raw maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

section Adapters

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem factorHalfBraiding_hom (a : ZMod 2) (X : EvenSubcategory ℝ (LinearCategory C)) :
    ((factorHalfBraiding C p hp a).β X).hom.hom = (p.moveFactor a X.obj).hom := by
  rcases parity_cases a with rfl | rfl <;> rfl

theorem factorHalfBraiding_inv (a : ZMod 2) (X : EvenSubcategory ℝ (LinearCategory C)) :
    ((factorHalfBraiding C p hp a).β X).inv.hom = (p.moveFactor a X.obj).inv := by
  rcases parity_cases a with rfl | rfl <;> rfl

theorem factorMultiplyCenterIso_hom (a b : ZMod 2) :
    (factorMultiplyCenterIso C p hp a b).hom.f.hom = (p.multiplyFactors a b).hom := rfl

theorem factorMultiplyCenterIso_inv (a b : ZMod 2) :
    (factorMultiplyCenterIso C p hp a b).inv.f.hom = (p.multiplyFactors a b).inv := by
  have he := (factorMultiplyCenterIso C p hp a b).hom_inv_id
  have he' := congrArg (fun f => f.f.hom) he
  change C.data.comp (p.multiplyFactors a b).hom
    (factorMultiplyCenterIso C p hp a b).inv.f.hom = C.data.id _ at he'
  have hh := congrArg (fun f => C.data.comp (p.multiplyFactors a b).inv f) he'
  simp only [← C.laws.comp_assoc, (hp.multiplyFactors_evenIso C.laws a b).inv_hom,
    C.laws.id_comp] at hh
  exact hh.trans (C.laws.comp_id _)

end Adapters

namespace PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem moveFactor_tensor (a : ZMod 2) (X Y : C.Obj) :
    (p.moveFactor a (C.tensorObj X Y)).hom =
      C.comp (C.associatorInv (p.factor a) X Y)
        (C.comp (C.tensorHom (p.moveFactor a X).hom (C.id Y))
          (C.comp (C.associatorHom X (p.factor a) Y)
            (C.comp (C.tensorHom (C.id X) (p.moveFactor a Y).hom)
              (C.associatorInv X Y (p.factor a))))) := by
  let A : WeaklyPointedSuperfusion := ⟨C, hC⟩
  let X' := evenObj ℝ (LinearCategory A) X
  let Y' := evenObj ℝ (LinearCategory A) Y
  have he := congrArg (fun f => f.hom) ((factorHalfBraiding A p hp a).monoidal X' Y')
  change ((factorHalfBraiding A p hp a).β (X' ⊗ Y')).hom.hom =
    C.comp (C.associatorInv (p.factor a) X Y)
      (C.comp (C.tensorHom ((factorHalfBraiding A p hp a).β X').hom.hom (C.id Y))
        (C.comp (C.associatorHom X (p.factor a) Y)
          (C.comp (C.tensorHom (C.id X) ((factorHalfBraiding A p hp a).β Y').hom.hom)
            (C.associatorInv X Y (p.factor a))))) at he
  simp only [factorHalfBraiding_hom] at he
  exact he

theorem multiplyFactors_central (a b : ZMod 2) (X : C.Obj) :
    C.comp (C.tensorHom (p.multiplyFactors a b).hom (C.id X))
      (p.moveFactor (a + b) X).hom =
    C.comp (C.associatorHom (p.factor a) (p.factor b) X)
      (C.comp (C.tensorHom (C.id (p.factor a)) (p.moveFactor b X).hom)
        (C.comp (C.associatorInv (p.factor a) X (p.factor b))
          (C.comp (C.tensorHom (p.moveFactor a X).hom (C.id (p.factor b)))
            (C.comp (C.associatorHom X (p.factor a) (p.factor b))
              (C.tensorHom (C.id X) (p.multiplyFactors a b).hom))))) := by
  let A : WeaklyPointedSuperfusion := ⟨C, hC⟩
  let X' := evenObj ℝ (LinearCategory A) X
  have he := congrArg (fun f => f.hom) ((factorMultiplyCenterHom A p hp a b).comm X')
  change C.comp (C.tensorHom (p.multiplyFactors a b).hom (C.id X))
      ((factorHalfBraiding A p hp (a + b)).β X').hom.hom =
    C.comp
      (C.comp (C.associatorHom (p.factor a) (p.factor b) X)
        (C.comp (C.tensorHom (C.id (p.factor a)) ((factorHalfBraiding A p hp b).β X').hom.hom)
          (C.comp (C.associatorInv (p.factor a) X (p.factor b))
            (C.comp (C.tensorHom ((factorHalfBraiding A p hp a).β X').hom.hom (C.id (p.factor b)))
              (C.associatorHom X (p.factor a) (p.factor b))))))
      (C.tensorHom (C.id X) (p.multiplyFactors a b).hom) at he
  simpa only [factorHalfBraiding_hom, hC.comp_assoc] using he

end PiLaws
end RMod.Classification
