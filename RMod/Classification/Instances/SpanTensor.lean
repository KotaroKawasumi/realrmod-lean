import RMod.Classification.Proofs.HomogeneousSpanTensor

/-!
# Tensor objects and maps in intrinsic product components

Membership of the tensor object in the product span is already proved.
Mathlib's full-subcategory wrapper retains the original ambient tensor
objects and morphisms, with no chosen decomposition in their data.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) (S T : SimpleObject C)

def spanTensorObj (X : HomogeneousSpanCategory C S.data.object)
    (Y : HomogeneousSpanCategory C T.data.object) :
    HomogeneousSpanCategory C (simpleTensorRepresentative C S T).data.object :=
  ⟨C.data.tensorObj X.obj Y.obj, inHomogeneousSpan_tensor C S T X.property Y.property⟩

def spanTensorHom {X X' : HomogeneousSpanCategory C S.data.object}
    {Y Y' : HomogeneousSpanCategory C T.data.object} (f : X ⟶ X') (g : Y ⟶ Y') :
    spanTensorObj C S T X Y ⟶ spanTensorObj C S T X' Y' :=
  ObjectProperty.homMk (C.data.tensorHom f.hom g.hom)

end RMod.Classification
