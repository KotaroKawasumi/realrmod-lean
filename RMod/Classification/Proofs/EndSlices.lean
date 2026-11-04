import RMod.Classification.Instances.EndSlices

/-!
# Evaluation of slices on pure tensor endomorphisms

Associator naturality moves the tensor endomorphism to the two factors.
The first interchange has the even unit vector as crossing factor; the
second has an identity. Thus no sign remains, even for inhomogeneous f, g
and caps. The cap evaluation then gives exactly the desired scalar times g.
-/

set_option autoImplicit false

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {L X : C.data.Obj}
  (p : DualPairing C L X) (Y : C.data.Obj)

attribute [local implicit_reducible] CategoryTheory.End

theorem endSlice_tensor (φ : Module.Dual ℝ (End (C := LinearCategory C) X))
    (f : End (C := LinearCategory C) X) (g : End (C := LinearCategory C) Y) :
    p.endSlice Y φ (C.data.tensorHom f g) = (φ f) • g := by
  have ha : C.data.comp
      (C.data.comp (C.data.associatorHom L X Y)
        (C.data.tensorHom (C.data.id L) (C.data.tensorHom f g))) (C.data.associatorInv L X Y) =
      C.data.tensorHom (C.data.tensorHom (C.data.id L) f) g := by
    rw [← C.laws.associator_naturality, C.laws.comp_assoc,
      C.laws.associator_hom_inv, C.laws.comp_id]
  change C.data.comp (p.slicePre Y)
    (C.data.comp (C.data.tensorHom (C.data.id L) (C.data.tensorHom f g)) (p.slicePost Y φ)) =
      C.data.smul (φ f) g
  calc
    _ = C.data.comp (C.data.leftUnitorInv Y)
        (C.data.comp
          (C.data.comp
            (C.data.comp (C.data.tensorHom p.endUnitVector (C.data.id Y))
              (C.data.comp (C.data.comp (C.data.associatorHom L X Y)
                (C.data.tensorHom (C.data.id L) (C.data.tensorHom f g)))
                (C.data.associatorInv L X Y)))
            (C.data.tensorHom (p.endCap φ) (C.data.id Y))) (C.data.leftUnitorHom Y)) := by
      simp only [slicePre, slicePost, C.laws.comp_assoc]
    _ = C.data.comp (C.data.leftUnitorInv Y)
        (C.data.comp
          (C.data.comp
            (C.data.comp (C.data.tensorHom p.endUnitVector (C.data.id Y))
              (C.data.tensorHom (C.data.tensorHom (C.data.id L) f) g))
            (C.data.tensorHom (p.endCap φ) (C.data.id Y))) (C.data.leftUnitorHom Y)) := by
      rw [ha]
    _ = C.data.comp (C.data.leftUnitorInv Y)
        (C.data.comp
          (C.data.tensorHom
            (C.data.comp (C.data.comp p.endUnitVector (C.data.tensorHom (C.data.id L) f))
              (p.endCap φ)) g) (C.data.leftUnitorHom Y)) := by
      rw [interchange_first_even C.laws _ _ _ _ p.endUnitVector_even, C.laws.id_comp,
        interchange_second_even C.laws _ _ _ _ (C.laws.id_even Y), C.laws.comp_id]
    _ = C.data.comp (C.data.leftUnitorInv Y)
        (C.data.comp (C.data.tensorHom (C.data.smul (φ f) (C.data.id C.data.tensorUnit)) g)
          (C.data.leftUnitorHom Y)) := by rw [p.endCap_evaluate]
    _ = C.data.smul (φ f) g := by
      rw [C.laws.tensor_smul_left, C.laws.smul_comp, C.laws.comp_smul,
        C.laws.left_unitor_naturality, ← C.laws.comp_assoc, C.laws.left_unitor_inv_hom,
        C.laws.id_comp]

end RMod.Classification.DualPairing
