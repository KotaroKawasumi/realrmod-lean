import RMod.Classification.Proofs.ParityUnit
import RMod.Classification.Proofs.Normalizers

/-!
# Associativity of all parity-factor multiplications

There are eight parity triples. If one factor is the unit, the identity
is ordinary unitor naturality or the triangle. The triple of odd factors
is exactly associativity of the signed contraction. The final equality
comparison records the actual associativity equality in ZMod 2.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem multiplyFactors_assoc (a b c : ZMod 2) :
    C.comp
      (C.comp (C.tensorHom (p.multiplyFactors a b).hom (C.id (p.factor c)))
        (p.multiplyFactors (a + b) c).hom)
      (IsoData.ofEq C (congrArg p.factor (add_assoc a b c))).hom =
    C.comp (C.associatorHom (p.factor a) (p.factor b) (p.factor c))
      (C.comp (C.tensorHom (C.id (p.factor a)) (p.multiplyFactors b c).hom)
        (p.multiplyFactors a (b + c)).hom) := by
  have htriangle (X Y : C.Obj) : C.comp (C.associatorHom X C.tensorUnit Y)
      (C.tensorHom (C.id X) (C.leftUnitorHom Y)) = C.tensorHom (C.rightUnitorHom X) (C.id Y) :=
    hC.triangle X Y
  rcases parity_cases a with rfl | rfl <;>
    rcases parity_cases b with rfl | rfl <;>
      rcases parity_cases c with rfl | rfl
  · change C.comp (C.comp (C.tensorHom (C.leftUnitorHom C.tensorUnit) (C.id C.tensorUnit))
      (C.leftUnitorHom C.tensorUnit)) (C.id C.tensorUnit) =
      C.comp (C.associatorHom C.tensorUnit C.tensorUnit C.tensorUnit)
        (C.comp (C.tensorHom (C.id C.tensorUnit) (C.leftUnitorHom C.tensorUnit))
          (C.leftUnitorHom C.tensorUnit))
    rw [hC.comp_id, ← hC.comp_assoc, htriangle, unitors_hom_equal hC]
  · change C.comp (C.comp (C.tensorHom (C.leftUnitorHom C.tensorUnit) (C.id p.object))
      (C.leftUnitorHom p.object)) (C.id p.object) =
      C.comp (C.associatorHom C.tensorUnit C.tensorUnit p.object)
        (C.comp (C.tensorHom (C.id C.tensorUnit) (C.leftUnitorHom p.object))
          (C.leftUnitorHom p.object))
    rw [hC.comp_id, ← hC.comp_assoc, htriangle, unitors_hom_equal hC]
  · change C.comp (C.comp (C.tensorHom (C.leftUnitorHom p.object) (C.id C.tensorUnit))
      (C.rightUnitorHom p.object)) (C.id p.object) =
      C.comp (C.associatorHom C.tensorUnit p.object C.tensorUnit)
        (C.comp (C.tensorHom (C.id C.tensorUnit) (C.rightUnitorHom p.object))
          (C.leftUnitorHom p.object))
    rw [hC.comp_id, hC.left_unitor_naturality, ← hC.comp_assoc, leftUnitor_tensor hC]
  · change C.comp (C.comp (C.tensorHom (C.leftUnitorHom p.object) (C.id p.object))
      p.contractionHom) (C.id C.tensorUnit) =
      C.comp (C.associatorHom C.tensorUnit p.object p.object)
        (C.comp (C.tensorHom (C.id C.tensorUnit) p.contractionHom)
          (C.leftUnitorHom C.tensorUnit))
    rw [hC.comp_id, hC.left_unitor_naturality, ← hC.comp_assoc, leftUnitor_tensor hC]
  · change C.comp (C.comp (C.tensorHom (C.rightUnitorHom p.object) (C.id C.tensorUnit))
      (C.rightUnitorHom p.object)) (C.id p.object) =
      C.comp (C.associatorHom p.object C.tensorUnit C.tensorUnit)
        (C.comp (C.tensorHom (C.id p.object) (C.leftUnitorHom C.tensorUnit))
          (C.rightUnitorHom p.object))
    rw [hC.comp_id, ← hC.comp_assoc, htriangle]
  · change C.comp (C.comp (C.tensorHom (C.rightUnitorHom p.object) (C.id p.object))
      p.contractionHom) (C.id C.tensorUnit) =
      C.comp (C.associatorHom p.object C.tensorUnit p.object)
        (C.comp (C.tensorHom (C.id p.object) (C.leftUnitorHom p.object)) p.contractionHom)
    rw [hC.comp_id, ← hC.comp_assoc, htriangle]
  · change C.comp (C.comp (C.tensorHom p.contractionHom (C.id C.tensorUnit))
      (C.leftUnitorHom C.tensorUnit)) (C.id C.tensorUnit) =
      C.comp (C.associatorHom p.object p.object C.tensorUnit)
        (C.comp (C.tensorHom (C.id p.object) (C.rightUnitorHom p.object)) p.contractionHom)
    rw [hC.comp_id, unitors_hom_equal hC, hC.right_unitor_naturality,
      rightUnitor_tensor hC, hC.comp_assoc]
  · change C.comp (C.comp (C.tensorHom p.contractionHom (C.id p.object))
      (C.leftUnitorHom p.object)) (C.id p.object) =
      C.comp (C.associatorHom p.object p.object p.object)
        (C.comp (C.tensorHom (C.id p.object) p.contractionHom) (C.rightUnitorHom p.object))
    rw [hC.comp_id, ← hC.comp_assoc]
    exact hp.contraction_assoc hC

end RMod.Classification.PiLaws
