import RMod.Hierarchy.Abstract.ParityShift
import RMod.Hierarchy.Instances.SuperTensorProduct

/-! The monoidal operations form an enriched functor with even coherence maps. -/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
namespace RMod.Legacy

structure MonoidalSuperstructureData (C : SupercategoryData) where
  tensor : SuperfunctorData (superTensorProductData C C) C
  unit : C.Obj
  associatorHom : ∀ X Y Z, EHom C (tensor.obj (tensor.obj (X, Y), Z))
    (tensor.obj (X, tensor.obj (Y, Z)))
  associatorInv : ∀ X Y Z, EHom C (tensor.obj (X, tensor.obj (Y, Z)))
    (tensor.obj (tensor.obj (X, Y), Z))
  leftHom : ∀ X, EHom C (tensor.obj (unit, X)) X
  leftInv : ∀ X, EHom C X (tensor.obj (unit, X))
  rightHom : ∀ X, EHom C (tensor.obj (X, unit)) X
  rightInv : ∀ X, EHom C X (tensor.obj (X, unit))

def eTensor {C : SupercategoryData} (d : MonoidalSuperstructureData C)
    {X X' Y Y' : C.Obj} (f : EHom C X X') (g : EHom C Y Y') :=
  (λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ d.tensor.map (X, Y) (X', Y')
def tTensor {C : SupercategoryData} (d : MonoidalSuperstructureData C)
    {X X' Y Y' : C.Obj} (f : THom C X X') (g : THom C Y Y') :
    THom C (d.tensor.obj (X, Y)) (d.tensor.obj (X', Y')) := fun a =>
  d.tensor.map (X, Y) (X', Y') a
    (∑ i : ZMod 2, GradedObject.Monoidal.ιTensorObj (C.Hom X X') (C.Hom Y Y')
      i (a - i) a (by abel) (f i ⊗ₜ[ℝ] g (a - i)))

structure MonoidalSuperstructureLaws (C : Supercategory)
    (d : MonoidalSuperstructureData C.data) : Prop where
  tensor : SuperfunctorLaws d.tensor
  associator_hom_inv : ∀ X Y Z, eComp C.data (d.associatorHom X Y Z)
    (d.associatorInv X Y Z) = C.data.id _
  associator_inv_hom : ∀ X Y Z, eComp C.data (d.associatorInv X Y Z)
    (d.associatorHom X Y Z) = C.data.id _
  left_hom_inv : ∀ X, eComp C.data (d.leftHom X) (d.leftInv X) = C.data.id _
  left_inv_hom : ∀ X, eComp C.data (d.leftInv X) (d.leftHom X) = C.data.id _
  right_hom_inv : ∀ X, eComp C.data (d.rightHom X) (d.rightInv X) = C.data.id _
  right_inv_hom : ∀ X, eComp C.data (d.rightInv X) (d.rightHom X) = C.data.id _
  associator_naturality : ∀ {X X' Y Y' Z Z'}
    (f : THom C.data X X') (g : THom C.data Y Y') (h : THom C.data Z Z'),
    tComp C.data (tTensor d (tTensor d f g) h) (evenPoint (d.associatorHom X' Y' Z')) =
      tComp C.data (evenPoint (d.associatorHom X Y Z)) (tTensor d f (tTensor d g h))
  left_naturality : ∀ {X Y} (f : THom C.data X Y),
    tComp C.data (tTensor d (evenPoint (C.data.id d.unit)) f) (evenPoint (d.leftHom Y)) =
      tComp C.data (evenPoint (d.leftHom X)) f
  right_naturality : ∀ {X Y} (f : THom C.data X Y),
    tComp C.data (tTensor d f (evenPoint (C.data.id d.unit))) (evenPoint (d.rightHom Y)) =
      tComp C.data (evenPoint (d.rightHom X)) f
  pentagon : ∀ W X Y Z,
    eComp C.data (eComp C.data (eTensor d (d.associatorHom W X Y) (C.data.id Z))
      (d.associatorHom W (d.tensor.obj (X, Y)) Z))
      (eTensor d (C.data.id W) (d.associatorHom X Y Z)) =
    eComp C.data (d.associatorHom (d.tensor.obj (W, X)) Y Z)
      (d.associatorHom W X (d.tensor.obj (Y, Z)))
  triangle : ∀ X Y, eComp C.data (d.associatorHom X d.unit Y)
    (eTensor d (C.data.id X) (d.leftHom Y)) = eTensor d (d.rightHom X) (C.data.id Y)
structure MonoidalSuperstructure (C : Supercategory) where
  data : MonoidalSuperstructureData C.data
  laws : MonoidalSuperstructureLaws C data
structure MonoidalSupercategoryData extends SupercategoryData where
  monoidal : MonoidalSuperstructureData toSupercategoryData
structure MonoidalSupercategoryLaws (d : MonoidalSupercategoryData) : Prop
    extends SupercategoryLaws d.toSupercategoryData where
  monoidal : MonoidalSuperstructureLaws ⟨d.toSupercategoryData, toSupercategoryLaws⟩ d.monoidal
structure MonoidalSupercategory where
  data : MonoidalSupercategoryData
  laws : MonoidalSupercategoryLaws data
structure MonoidalPiSupercategoryData extends PiSupercategoryData where
  monoidal : MonoidalSuperstructureData toSupercategoryData
structure MonoidalPiSupercategoryLaws (d : MonoidalPiSupercategoryData) : Prop
    extends PiSupercategoryLaws d.toPiSupercategoryData where
  monoidal : MonoidalSuperstructureLaws ⟨d.toSupercategoryData, toSupercategoryLaws⟩ d.monoidal
structure MonoidalPiSupercategory where
  data : MonoidalPiSupercategoryData
  laws : MonoidalPiSupercategoryLaws data

def MonoidalSupercategory.super (C : MonoidalSupercategory) : Supercategory :=
  ⟨C.data.toSupercategoryData, C.laws.toSupercategoryLaws⟩
def MonoidalPiSupercategory.monoidal (C : MonoidalPiSupercategory) : MonoidalSupercategory :=
  ⟨⟨C.data.toSupercategoryData, C.data.monoidal⟩,
    ⟨C.laws.toSupercategoryLaws, C.laws.monoidal⟩⟩

end RMod.Legacy
