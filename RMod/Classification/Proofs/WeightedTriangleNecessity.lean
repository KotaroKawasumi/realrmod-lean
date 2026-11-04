import RMod.Classification.Proofs.ParityTriangle
import RMod.Classification.Proofs.ScalarFaithfulness

/-!
# The triangle forces the middle normalization of omega

The unweighted local triangle is already known. Inserting an arbitrary
scalar multiplies its first route by that scalar. If the second route
is nonzero, equality of the two routes forces the scalar to be one.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

include hp

theorem localAssociator_triangle_scalar_of_eq (X Y : C.data.Obj) (a : ZMod 2) (ω : ℝˣ)
    (hne : C.data.tensorHom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
          (C.data.rightUnitorHom X)) (C.data.id Y)) (C.data.id (p.factor a)) ≠ C.data.zero)
    (he : C.data.comp (p.localAssociator X C.data.tensorUnit Y 0 a 0 a rfl ω).hom
      (C.data.tensorHom
        (C.data.tensorHom (C.data.id X)
          (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y))
            (C.data.leftUnitorHom Y))) (C.data.id (p.factor a))) =
    C.data.tensorHom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
          (C.data.rightUnitorHom X)) (C.data.id Y)) (C.data.id (p.factor a))) : ω = 1 := by
  have h₁ := localAssociator_triangle C p hp X Y a
  dsimp only [PiData.localAssociator, IsoData.scale] at he h₁
  simp only [Units.val_one, C.laws.one_smul] at h₁
  rw [C.laws.smul_comp, h₁] at he
  apply Units.ext
  exact raw_smul_injective C _ hne (he.trans (C.laws.one_smul _).symm)

end RMod.Classification
