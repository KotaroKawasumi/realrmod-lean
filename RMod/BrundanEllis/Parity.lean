import RMod.BrundanEllis.MonoidalBridge

/-! The parity object and its Mathlib enriched left-tensor functor.
An existing odd shift supplies the parity object at the unit. Conversely, the
chosen parity object determines the shift functor without a second choice of
objects or Hom maps. Odd supernatural comparison laws are a separate next step. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
universe u

/-- Definition 1.12's odd isomorphism is the old parity comparison at the unit. -/
@[implicit_reducible] def piObjectOfShift (C : Type u) [SuperCategory C]
    [MonoidalCategory (Even C)] [RMod.PiSuperCategory C] : MonoidalPiSuperCategory C where
  pi := (RMod.PiSuperCategory.parityShift (C := C)).functor.obj (𝟙_ (Even C))
  hom := (RMod.PiSuperCategory.parityShift (C := C)).inv (𝟙_ (Even C))
  inv := (RMod.PiSuperCategory.parityShift (C := C)).hom.app (𝟙_ (Even C))
  hom_inv := (RMod.PiSuperCategory.parityShift (C := C)).inv_hom (𝟙_ (Even C))
  inv_hom := (RMod.PiSuperCategory.parityShift (C := C)).hom_inv (𝟙_ (Even C))

section
variable (C : Type u) [SuperCategory C] [MonoidalCategory (Even C)]
  [M : MonoidalSuperCategory C] [P : MonoidalPiSuperCategory C]

/-- Left tensor by the parity object, as a genuine Mathlib enriched functor. -/
def piFunctor : SuperFunctor C C :=
  (RMod.insertLeft SuperVec P.pi).comp SuperVec
    (RMod.alignedTensor SuperVec M.tensor M.tensor_objects)

/-- The object part is fixed to the ordinary Mathlib tensor. -/
theorem piFunctor_obj (X : C) :
    (piFunctor C).obj X = (evenObj C P.pi ⊗ evenObj C X : Even C) := rfl

/-- The Hom map is the identity of the parity object tensored with the input. -/
theorem piFunctor_map (X Y : C) :
    (piFunctor C).map X Y =
      (λ_ (SHom C X Y)).inv ≫ (eId SuperVec P.pi ⊗ₘ 𝟙 (SHom C X Y)) ≫
        enrichedTensorMap M.tensor M.tensor_objects P.pi P.pi X Y := rfl

end
end RMod.BrundanEllis
