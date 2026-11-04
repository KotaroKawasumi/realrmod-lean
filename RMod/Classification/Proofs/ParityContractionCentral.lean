import RMod.Classification.Proofs.ParityContraction

/-!
# Compatibility of contraction with moving two parity factors

Moving both parity factors past an object and then contracting them gives
the same map as contracting first. Odd deletion expresses both routes in
terms of z and right-z. The middle deletion identity, the even naturality
of the central comparison, and cancellation of associators prove the
equation with every structural map displayed.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

attribute [local implicit_reducible] PiData.shiftObj

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem contraction_tensor_left (X : C.Obj) :
    C.comp (C.tensorHom p.contractionHom (C.id X)) (C.leftUnitorHom X) =
      C.comp (C.associatorHom p.object p.object X)
        (C.comp (p.zHom (C.tensorObj p.object X)) (p.zHom X)) := by
  rw [hp.contraction_eq_z hC]
  have ht := (tensorRightLaws ⟨C, hC⟩ X).map_comp (p.zHom p.object) p.hom
  change C.tensorHom (C.comp (p.zHom p.object) p.hom) (C.id X) =
    C.comp (C.tensorHom (p.zHom p.object) (C.id X)) (C.tensorHom p.hom (C.id X)) at ht
  rw [ht, hC.comp_assoc]
  change C.comp (C.tensorHom (p.zHom p.object) (C.id X)) (p.zHom X) = _
  rw [← z_tensor hC p.object X, hC.comp_assoc]

theorem contraction_tensor_right (X : C.Obj) :
    C.comp (C.associatorHom X p.object p.object)
      (C.comp (C.tensorHom (C.id X) p.contractionHom) (C.rightUnitorHom X)) =
      C.comp (C.tensorHom (p.rightZHom X) (C.id p.object)) (p.rightZHom X) := by
  rw [hp.contraction_eq_z hC]
  have ht := (tensorLeftLaws ⟨C, hC⟩ X).map_comp (p.zHom p.object) p.hom
  change C.tensorHom (C.id X) (C.comp (p.zHom p.object) p.hom) =
    C.comp (C.tensorHom (C.id X) (p.zHom p.object)) (C.tensorHom (C.id X) p.hom) at ht
  rw [ht, hC.comp_assoc, ← hC.comp_assoc, rightZ_middle hC]
  rfl

theorem contraction_central (X : C.Obj) :
    C.comp (C.tensorHom p.contractionHom (C.id X)) (C.leftUnitorHom X) =
      C.comp (C.associatorHom p.object p.object X)
        (C.comp (C.tensorHom (C.id p.object) (p.centralHom X))
          (C.comp (C.associatorInv p.object X p.object)
            (C.comp (C.tensorHom (p.centralHom X) (C.id p.object))
              (C.comp (C.associatorHom X p.object p.object)
                (C.comp (C.tensorHom (C.id X) p.contractionHom) (C.rightUnitorHom X)))))) := by
  have ht := (tensorRightLaws ⟨C, hC⟩ p.object).map_comp (p.centralHom X) (p.rightZHom X)
  change C.tensorHom (C.comp (p.centralHom X) (p.rightZHom X)) (C.id p.object) =
    C.comp (C.tensorHom (p.centralHom X) (C.id p.object))
      (C.tensorHom (p.rightZHom X) (C.id p.object)) at ht
  have hn := hp.z_naturality hC (p.centralHom X) (hp.central_hom_even hC X)
  change C.comp (C.tensorHom (C.id p.object) (p.centralHom X))
      (p.zHom (C.tensorObj X p.object)) =
    C.smul ((-1 : ℝ) ^ (0 : ZMod 2).val)
      (C.comp (p.zHom (C.tensorObj p.object X)) (p.centralHom X)) at hn
  simp only [ZMod.val_zero, pow_zero, hC.one_smul] at hn
  rw [hp.contraction_tensor_left hC X, hp.contraction_tensor_right hC X,
    ← hC.comp_assoc (C.tensorHom (p.centralHom X) (C.id p.object)), ← ht,
    hp.central_rightZ hC, ← z_tensor hC X p.object, hC.comp_assoc,
    ← hC.comp_assoc (C.associatorInv p.object X p.object), hC.associator_inv_hom,
    hC.id_comp, ← hC.comp_assoc (C.tensorHom (C.id p.object) (p.centralHom X)),
    hn, hC.comp_assoc, hp.central_rightZ hC]

end RMod.Classification.PiLaws
