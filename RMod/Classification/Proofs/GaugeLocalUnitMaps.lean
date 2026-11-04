import RMod.Classification.Proofs.GaugeLocalUnit

/-!
# Unit coherence for the actual raw gauge maps

Take underlying full-Hom maps in the checked even diagrams. The bridge
to the scalar-free even expression retains the raw tensorator with
beta=1, rather than replacing it by an unspecified unit comparison.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem gaugeLocalTensorator_left_unit (Y : C.data.Obj) (a : ZMod 2) :
    C.data.comp (C.data.tensorHom
      (C.data.tensorHom (C.data.rightUnitorInv C.data.tensorUnit)
        (C.data.id (C.data.tensorObj Y (p.factor a)))) (C.data.id C.data.tensorUnit))
      (C.data.comp (p.gaugeLocalTensorator C.data.tensorUnit Y 0 a 0 0 a (by simp) 1).hom
        (C.data.tensorHom
          (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y))
            (C.data.leftUnitorHom Y)) (C.data.id (p.factor a)))) =
    C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit
      (C.data.tensorObj Y (p.factor a)))) (C.data.leftUnitorHom (C.data.tensorObj Y (p.factor a))) := by
  have he := congrArg (fun f => f.hom)
    (scalarFreeGaugeEven_left_unit C p hp (evenObj ℝ (LinearCategory C) Y) a)
  change C.data.comp (C.data.tensorHom
    (C.data.tensorHom (C.data.rightUnitorInv C.data.tensorUnit)
      (C.data.id (C.data.tensorObj Y (p.factor a)))) (C.data.id C.data.tensorUnit))
    (C.data.comp (scalarFreeGaugeEvenIso C p hp (𝟙_ (EvenSubcategory ℝ (LinearCategory C)))
      (evenObj ℝ (LinearCategory C) Y) 0 a 0 0 a (by simp)).hom.hom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y))
          (C.data.leftUnitorHom Y)) (C.data.id (p.factor a)))) = _ at he
  rw [scalarFreeGaugeEvenIso_hom] at he
  exact he

theorem gaugeLocalTensorator_right_unit (X : C.data.Obj) (a : ZMod 2) :
    C.data.comp (C.data.tensorHom
      (C.data.tensorHom (C.data.id (C.data.tensorObj X (p.factor a)))
        (C.data.rightUnitorInv C.data.tensorUnit)) (C.data.id C.data.tensorUnit))
      (C.data.comp (p.gaugeLocalTensorator X C.data.tensorUnit a 0 0 0 a (by simp) 1).hom
        (C.data.tensorHom
          (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
            (C.data.rightUnitorHom X)) (C.data.id (p.factor a)))) =
    C.data.comp (C.data.rightUnitorHom (C.data.tensorObj
      (C.data.tensorObj X (p.factor a)) C.data.tensorUnit)) (C.data.rightUnitorHom (C.data.tensorObj X (p.factor a))) := by
  have he := congrArg (fun f => f.hom)
    (scalarFreeGaugeEven_right_unit C p hp (evenObj ℝ (LinearCategory C) X) a)
  change C.data.comp (C.data.tensorHom
    (C.data.tensorHom (C.data.id (C.data.tensorObj X (p.factor a)))
      (C.data.rightUnitorInv C.data.tensorUnit)) (C.data.id C.data.tensorUnit))
    (C.data.comp (scalarFreeGaugeEvenIso C p hp (evenObj ℝ (LinearCategory C) X)
      (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) a 0 0 0 a (by simp)).hom.hom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
          (C.data.rightUnitorHom X)) (C.data.id (p.factor a)))) = _ at he
  rw [scalarFreeGaugeEvenIso_hom] at he
  exact he

end RMod.Classification
