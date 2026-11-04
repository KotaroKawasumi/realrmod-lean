import RMod.Hierarchy.Abstract.MonoidalSupercategory
import RMod.Hierarchy.Instances.HomogeneousPoints

/-!
# Tensoring even morphisms

The tensor unit's diagonal is compatible with the braided tensor comparison.
Consequently, the specified superfunctor induces the ordinary bifunctor on
morphisms of degree zero.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open scoped TensorProduct
namespace RMod.Legacy

@[reassoc]
theorem unitDiagonal_tensorμ :
    (λ_ (𝟙_ SuperVec)).inv ≫
      ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) ≫
      tensorμ (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) (𝟙_ SuperVec) =
    (λ_ (𝟙_ SuperVec)).inv ≫
      ((λ_ (𝟙_ SuperVec)).inv ⊗ₘ (λ_ (𝟙_ SuperVec)).inv) := by
  unfold tensorμ
  erw [braiding_tensorUnit_left]
  monoidal

theorem pairedEven_comp (C D : SupercategoryData) {X Y Z : C.Obj} {X' Y' Z' : D.Obj}
    (f : EHom C X Y) (g : EHom D X' Y') (h : EHom C Y Z) (k : EHom D Y' Z') :
    eComp (superTensorProductData C D) (X := (X, X')) (Y := (Y, Y')) (Z := (Z, Z'))
      ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g)) ((λ_ (𝟙_ SuperVec)).inv ≫ (h ⊗ₘ k)) =
      (λ_ (𝟙_ SuperVec)).inv ≫ (eComp C f h ⊗ₘ eComp D g k) := by
  dsimp only [eComp, superTensorProductData]
  rw [← tensorHom_comp_tensorHom, assoc, tensorμ_natural_assoc,
    unitDiagonal_tensorμ_assoc]
  simp only [← tensorHom_comp_tensorHom]

theorem eComp_id (C : Supercategory) {X Y : C.data.Obj} (f : EHom C.data X Y) :
    eComp C.data f (C.data.id Y) = f :=
  @Category.comp_id (Even C) _ (evenObj C X) (evenObj C Y) f

theorem id_eComp (C : Supercategory) {X Y : C.data.Obj} (f : EHom C.data X Y) :
    eComp C.data (C.data.id X) f = f :=
  @Category.id_comp (Even C) _ (evenObj C X) (evenObj C Y) f

theorem eTensor_id {C : Supercategory} (d : MonoidalSuperstructureData C.data)
    (h : MonoidalSuperstructureLaws C d) (X Y : C.data.Obj) :
    eTensor d (C.data.id X) (C.data.id Y) = C.data.id (d.tensor.obj (X, Y)) :=
  h.tensor.map_id (X, Y)

theorem eMap_comp {C D : SupercategoryData} (F : SuperfunctorData C D)
    (hF : SuperfunctorLaws F) {X Y Z : C.Obj} (f : EHom C X Y) (g : EHom C Y Z) :
    eComp D (f ≫ F.map X Y) (g ≫ F.map Y Z) = eComp C f g ≫ F.map X Z := by
  dsimp only [eComp]
  rw [← tensorHom_comp_tensorHom, assoc, ← hF.map_comp]
  simp only [assoc]

theorem eTensor_comp {C : Supercategory} (d : MonoidalSuperstructureData C.data)
    (h : MonoidalSuperstructureLaws C d) {X Y Z X' Y' Z' : C.data.Obj}
    (f : EHom C.data X Y) (g : EHom C.data X' Y')
    (q : EHom C.data Y Z) (r : EHom C.data Y' Z') :
    eComp C.data (eTensor d f g) (eTensor d q r) =
      eTensor d (eComp C.data f q) (eComp C.data g r) := by
  change eComp C.data
    (((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g)) ≫ d.tensor.map (X, X') (Y, Y'))
    (((λ_ (𝟙_ SuperVec)).inv ≫ (q ⊗ₘ r)) ≫ d.tensor.map (Y, Y') (Z, Z')) = _
  exact (eMap_comp d.tensor h.tensor (X := (X, X')) (Y := (Y, Y')) (Z := (Z, Z'))
    ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g))
    ((λ_ (𝟙_ SuperVec)).inv ≫ (q ⊗ₘ r))).trans
      (congrArg (fun m => m ≫ d.tensor.map (X, X') (Z, Z'))
        (pairedEven_comp C.data C.data f g q r))

end RMod.Legacy
