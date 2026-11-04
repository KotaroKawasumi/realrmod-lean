import RMod.Classification.Instances.DualHomEquivalences

/-!
# The Hom spaces used in the tensor dimension calculation

A right dual pair X,Y identifies End(X) with Hom(1,X tensor Y).
The same adjunction and the associator identify End(Z tensor X) with
Hom(Z,Z tensor (X tensor Y)). All maps use the given duality and tensor
comparisons and therefore require no additional choice.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.DualPairing

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{u, v}} {X Y : C.data.Obj} (p : DualPairing C X Y)

attribute [local implicit_reducible] CategoryTheory.End
  tensorRightData tensorRightSuperfunctor Superfunctor.toFunctor

def rightEndHomLinearEquiv :
    End (C := LinearCategory C) X ≃ₗ[ℝ]
      @Quiver.Hom (LinearCategory C) inferInstance C.data.tensorUnit (C.data.tensorObj X Y) := by
  let e : @Iso (LinearCategory C) _ X (C.data.tensorObj C.data.tensorUnit X) :=
    ⟨C.data.leftUnitorInv X, C.data.leftUnitorHom X,
      C.laws.left_unitor_inv_hom X, C.laws.left_unitor_hom_inv X⟩
  exact (Linear.homCongr ℝ e (Iso.refl (C := LinearCategory C) X)).trans
    (p.rightHomLinearEquiv C.data.tensorUnit X)

def tensorEndHomLinearEquiv (Z : LinearCategory C) :
    End (C := LinearCategory C) (C.data.tensorObj Z X) ≃ₗ[ℝ]
      @Quiver.Hom (LinearCategory C) inferInstance Z
        (C.data.tensorObj Z (C.data.tensorObj X Y)) := by
  let e : @Iso (LinearCategory C) _ (C.data.tensorObj (C.data.tensorObj Z X) Y)
      (C.data.tensorObj Z (C.data.tensorObj X Y)) :=
    ⟨C.data.associatorHom Z X Y, C.data.associatorInv Z X Y,
      C.laws.associator_hom_inv Z X Y, C.laws.associator_inv_hom Z X Y⟩
  exact (p.rightHomLinearEquiv Z (C.data.tensorObj Z X)).trans
    (Linear.homCongr ℝ (Iso.refl (C := LinearCategory C) Z) e)

end RMod.Classification.DualPairing
