import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Superfusion.Category.Monoidal

/-!
# The even subcategory of a supercategory

This file extracts the ordinary category whose objects are those of a
supercategory and whose morphisms are the parity-zero morphisms.  This is the
category in which ordinary categorical notions such as subobjects and
simplicity are interpreted.  The construction reuses Mathlib's
`MorphismProperty.WideSubcategory`.
-/

universe v u

open CategoryTheory

namespace Superfusion.Category

variable (K : Type*) [Field K]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear K C]
  [Supercategory K C]

/-- The morphism property selecting the even part of every Hom superspace. -/
def evenMorphismProperty : MorphismProperty C :=
  fun {X Y} f => f ∈ homGrade K X Y 0

instance : (evenMorphismProperty K C).IsMultiplicative where
  id_mem X := Supercategory.id_mem_even X
  comp_mem f g hf hg := by
    simpa only [evenMorphismProperty, homGrade, zero_add] using
      Supercategory.comp_mem f g hf hg

/-- The ordinary category with the same objects as `C` and only even
morphisms. -/
abbrev EvenSubcategory := WideSubcategory (evenMorphismProperty K C)

/-- Regard an object of a supercategory as an object of its even
subcategory. -/
abbrev evenObj (X : C) : EvenSubcategory K C := ⟨X⟩

private def evenHomEquiv {X Y : EvenSubcategory K C} :
    (X ⟶ Y) ≃ (homGrade K X.obj Y.obj 0) where
  toFun f := ⟨f.hom, f.property⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {X Y : EvenSubcategory K C} : AddCommGroup (X ⟶ Y) :=
  Equiv.addCommGroup (evenHomEquiv K C)

@[simp] lemma even_zero_hom {X Y : EvenSubcategory K C} :
    (0 : X ⟶ Y).hom = 0 := rfl

@[simp] lemma even_add_hom {X Y : EvenSubcategory K C} (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl

@[simp] lemma even_neg_hom {X Y : EvenSubcategory K C} (f : X ⟶ Y) :
    (-f).hom = -f.hom := rfl

instance : Preadditive (EvenSubcategory K C) where
  add_comp _ _ _ f g h := by
    apply WideSubcategory.hom_ext
    exact Preadditive.add_comp _ _ _ f.hom g.hom h.hom
  comp_add _ _ _ f g h := by
    apply WideSubcategory.hom_ext
    exact Preadditive.comp_add _ _ _ f.hom g.hom h.hom

instance {X Y : EvenSubcategory K C} : Module K (X ⟶ Y) :=
  Equiv.module K (evenHomEquiv K C)

@[simp] lemma even_smul_hom {X Y : EvenSubcategory K C} (r : K) (f : X ⟶ Y) :
    (r • f).hom = r • f.hom := rfl

instance : Linear K (EvenSubcategory K C) where
  smul_comp _ _ _ r f g := by
    apply WideSubcategory.hom_ext
    exact Linear.smul_comp _ _ _ r f.hom g.hom
  comp_smul _ _ _ f r g := by
    apply WideSubcategory.hom_ext
    exact Linear.comp_smul _ _ _ f.hom r g.hom

instance evenInclusion_additive :
    (wideSubcategoryInclusion (evenMorphismProperty K C)).Additive where
  map_add := rfl

instance evenInclusion_linear :
    (wideSubcategoryInclusion (evenMorphismProperty K C)).Linear K where
  map_smul := by intros; rfl

/-- A super-simple object is a simple object in the even subcategory.  In
particular, odd endomorphisms do not create spurious subobjects of a
Majorana/Q-type simple. -/
def IsSuperSimple (X : C) : Prop :=
  Simple (evenObj K C X)

/-- Regard an ambient even isomorphism as an isomorphism in the even
subcategory. -/
def evenSubcategoryIsoOfEvenIso
    {𝕜 : Type*} [Field 𝕜]
    {D : Type u} [Category.{v} D] [Preadditive D] [Linear 𝕜 D]
    [Supercategory 𝕜 D] {X Y : D}
    (e : EvenIso 𝕜 X Y) :
    evenObj 𝕜 D X ≅ evenObj 𝕜 D Y where
  hom := ⟨e.iso.hom, e.hom_mem⟩
  inv := ⟨e.iso.inv, e.inv_mem⟩

/-- Regard an isomorphism in the even subcategory as an ambient even
isomorphism. -/
def evenIsoOfEvenSubcategoryIso
    {𝕜 : Type*} [Field 𝕜]
    {D : Type u} [Category.{v} D] [Preadditive D] [Linear 𝕜 D]
    [Supercategory 𝕜 D] {X Y : D}
    (e : evenObj 𝕜 D X ≅ evenObj 𝕜 D Y) :
    EvenIso 𝕜 X Y where
  iso :=
    (wideSubcategoryInclusion
      (evenMorphismProperty 𝕜 D)).mapIso e
  hom_mem := e.hom.property
  inv_mem := e.inv.property

section Monoidal

open MonoidalCategory

variable [MonoidalCategoryStruct C] [MonoidalSupercategory K C]

include K

private lemma tensor_zero_right {X Y Z W : C} (f : X ⟶ Y) :
    f ⊗ₘ (0 : Z ⟶ W) = 0 := by
  have h := MonoidalSupercategory.tensor_add_right (K := K)
    f (0 : Z ⟶ W) 0
  simp only [zero_add] at h
  apply add_left_cancel (a := f ⊗ₘ (0 : Z ⟶ W))
  simpa using h.symm

private lemma tensor_zero_left {X Y Z W : C} (g : Z ⟶ W) :
    (0 : X ⟶ Y) ⊗ₘ g = 0 := by
  have h := MonoidalSupercategory.tensor_add_left (K := K)
    (0 : X ⟶ Y) 0 g
  simp only [zero_add] at h
  apply add_left_cancel (a := (0 : X ⟶ Y) ⊗ₘ g)
  simpa using h.symm

instance evenMonoidalCategoryStruct :
    MonoidalCategoryStruct (EvenSubcategory K C) where
  tensorObj X Y := evenObj K C (X.obj ⊗ Y.obj)
  whiskerLeft X {_ _} f :=
    ⟨X.obj ◁ f.hom, by
      rw [MonoidalSupercategory.whiskerLeft_eq (K := K)]
      simpa only [evenMorphismProperty, zero_add] using
        MonoidalSupercategory.tensorHom_mem (K := K) (𝟙 X.obj) f.hom
          (Supercategory.id_mem_even X.obj) f.property⟩
  whiskerRight {_ _} f Z :=
    ⟨f.hom ▷ Z.obj, by
      rw [MonoidalSupercategory.whiskerRight_eq (K := K)]
      simpa only [evenMorphismProperty, zero_add] using
        MonoidalSupercategory.tensorHom_mem (K := K) f.hom (𝟙 Z.obj)
          f.property (Supercategory.id_mem_even Z.obj)⟩
  tensorHom f g :=
    ⟨f.hom ⊗ₘ g.hom, by
      simpa only [evenMorphismProperty, zero_add] using
        MonoidalSupercategory.tensorHom_mem (K := K) f.hom g.hom f.property g.property⟩
  tensorUnit := evenObj K C (𝟙_ C)
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj)
    (MonoidalSupercategory.associator_hom_mem (K := K) X.obj Y.obj Z.obj)
    (MonoidalSupercategory.associator_inv_mem (K := K) X.obj Y.obj Z.obj)
  leftUnitor X := isoMk (λ_ X.obj)
    (MonoidalSupercategory.leftUnitor_hom_mem (K := K) X.obj)
    (MonoidalSupercategory.leftUnitor_inv_mem (K := K) X.obj)
  rightUnitor X := isoMk (ρ_ X.obj)
    (MonoidalSupercategory.rightUnitor_hom_mem (K := K) X.obj)
    (MonoidalSupercategory.rightUnitor_inv_mem (K := K) X.obj)

/-- Restricted to even morphisms, super-interchange has no sign, so the even
subcategory is an ordinary monoidal category. -/
instance evenMonoidalCategory : MonoidalCategory (EvenSubcategory K C) := by
  apply MonoidalCategory.ofTensorHom
  · intro X Y
    apply WideSubcategory.hom_ext
    exact MonoidalSupercategory.tensor_id (K := K) X.obj Y.obj
  · intro X Y Z f
    apply WideSubcategory.hom_ext
    exact (MonoidalSupercategory.whiskerLeft_eq (K := K) X.obj f.hom).symm
  · intro X Y f Z
    apply WideSubcategory.hom_ext
    exact (MonoidalSupercategory.whiskerRight_eq (K := K) f.hom Z.obj).symm
  · intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
    apply WideSubcategory.hom_ext
    change (f₁.hom ⊗ₘ f₂.hom) ≫ (g₁.hom ⊗ₘ g₂.hom) =
      (f₁.hom ≫ g₁.hom) ⊗ₘ (f₂.hom ≫ g₂.hom)
    simpa only [koszulSign, ZMod.val_zero, mul_zero, pow_zero, one_smul] using
      MonoidalSupercategory.super_interchange (K := K)
        g₁.hom g₂.hom f₁.hom f₂.hom g₂.property f₁.property
  · intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
    apply WideSubcategory.hom_ext
    exact MonoidalSupercategory.associator_naturality (K := K) f₁.hom f₂.hom f₃.hom
  · intro X Y f
    apply WideSubcategory.hom_ext
    change (𝟙 (𝟙_ C) ⊗ₘ f.hom) ≫ (λ_ Y.obj).hom = (λ_ X.obj).hom ≫ f.hom
    have h := MonoidalSupercategory.leftUnitor_naturality (K := K) f.hom
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K)] at h
    exact h
  · intro X Y f
    apply WideSubcategory.hom_ext
    change (f.hom ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y.obj).hom = (ρ_ X.obj).hom ≫ f.hom
    have h := MonoidalSupercategory.rightUnitor_naturality (K := K) f.hom
    rw [MonoidalSupercategory.whiskerRight_eq (K := K)] at h
    exact h
  · intro W X Y Z
    apply WideSubcategory.hom_ext
    change ((α_ W.obj X.obj Y.obj).hom ⊗ₘ 𝟙 Z.obj) ≫
        (α_ W.obj (X.obj ⊗ Y.obj) Z.obj).hom ≫
        (𝟙 W.obj ⊗ₘ (α_ X.obj Y.obj Z.obj).hom) =
      (α_ (W.obj ⊗ X.obj) Y.obj Z.obj).hom ≫
        (α_ W.obj X.obj (Y.obj ⊗ Z.obj)).hom
    have h := MonoidalSupercategory.pentagon (K := K) W.obj X.obj Y.obj Z.obj
    rw [MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K)] at h
    exact h
  · intro X Y
    apply WideSubcategory.hom_ext
    change (α_ X.obj (𝟙_ C) Y.obj).hom ≫
        (𝟙 X.obj ⊗ₘ (λ_ Y.obj).hom) =
      (ρ_ X.obj).hom ⊗ₘ 𝟙 Y.obj
    have h := MonoidalSupercategory.triangle (K := K) X.obj Y.obj
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)] at h
    exact h

instance evenMonoidalPreadditive :
    MonoidalPreadditive (EvenSubcategory K C) where
  whiskerLeft_zero := by
    intro X Y Z
    apply WideSubcategory.hom_ext
    change X.obj ◁ (0 : Y.obj ⟶ Z.obj) = 0
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K)]
    exact tensor_zero_right K C (𝟙 X.obj)
  zero_whiskerRight := by
    intro X Y Z
    apply WideSubcategory.hom_ext
    change (0 : Y.obj ⟶ Z.obj) ▷ X.obj = 0
    rw [MonoidalSupercategory.whiskerRight_eq (K := K)]
    exact tensor_zero_left K C (𝟙 X.obj)
  whiskerLeft_add := by
    intro X Y Z f g
    apply WideSubcategory.hom_ext
    change X.obj ◁ (f.hom + g.hom) = X.obj ◁ f.hom + X.obj ◁ g.hom
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K)]
    exact MonoidalSupercategory.tensor_add_right (K := K) (𝟙 X.obj) f.hom g.hom
  add_whiskerRight := by
    intro X Y Z f g
    apply WideSubcategory.hom_ext
    change (f.hom + g.hom) ▷ X.obj = f.hom ▷ X.obj + g.hom ▷ X.obj
    rw [MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    exact MonoidalSupercategory.tensor_add_left (K := K) f.hom g.hom (𝟙 X.obj)

instance evenMonoidalLinear :
    MonoidalLinear K (EvenSubcategory K C) where
  whiskerLeft_smul := by
    intro X Y Z r f
    apply WideSubcategory.hom_ext
    change X.obj ◁ (r • f.hom) = r • (X.obj ◁ f.hom)
    rw [MonoidalSupercategory.whiskerLeft_eq (K := K),
      MonoidalSupercategory.whiskerLeft_eq (K := K)]
    exact MonoidalSupercategory.tensor_smul_right (K := K) r (𝟙 X.obj) f.hom
  smul_whiskerRight := by
    intro r Y Z f X
    apply WideSubcategory.hom_ext
    change (r • f.hom) ▷ X.obj = r • (f.hom ▷ X.obj)
    rw [MonoidalSupercategory.whiskerRight_eq (K := K),
      MonoidalSupercategory.whiskerRight_eq (K := K)]
    exact MonoidalSupercategory.tensor_smul_left (K := K) r f.hom (𝟙 X.obj)

namespace SuperExactPairing

variable {K C}
variable {X X' Y Y' : C}

/-- Regard an even exact pairing in a monoidal supercategory as Mathlib's
ordinary exact pairing in the even subcategory.

The two structures have the same coevaluation, evaluation, and snake
identities.  This adapter merely retains the degree-zero witnesses on the
two morphisms. -/
@[implicit_reducible]
def toEven (p : SuperExactPairing K X Y) :
    ExactPairing (evenObj K C X) (evenObj K C Y) where
  coevaluation' := ⟨p.coeval, p.coeval_mem⟩
  evaluation' := ⟨p.eval, p.eval_mem⟩
  coevaluation_evaluation' := by
    apply WideSubcategory.hom_ext
    exact p.coevaluation_evaluation
  evaluation_coevaluation' := by
    apply WideSubcategory.hom_ext
    exact p.evaluation_coevaluation

/-- Recover a super exact pairing from an ordinary exact pairing in the
even subcategory. -/
def ofEven
    (p : ExactPairing (evenObj K C X) (evenObj K C Y)) :
    SuperExactPairing K X Y where
  coeval := p.coevaluation'.hom
  eval := p.evaluation'.hom
  coeval_mem := p.coevaluation'.property
  eval_mem := p.evaluation'.property
  coevaluation_evaluation := by
    exact congrArg (fun f => f.hom) p.coevaluation_evaluation'
  evaluation_coevaluation := by
    exact congrArg (fun f => f.hom) p.evaluation_coevaluation'

/-- Transport the first object of a super exact pairing across an even
isomorphism. -/
def congrLeft
    (e : EvenIso K X X') (p : SuperExactPairing K X' Y) :
    SuperExactPairing K X Y := by
  letI : ExactPairing (evenObj K C X') (evenObj K C Y) :=
    p.toEven
  exact ofEven
    (exactPairingCongrLeft
      (evenSubcategoryIsoOfEvenIso e))

/-- Transport the second object of a super exact pairing across an even
isomorphism. -/
def congrRight
    (e : EvenIso K Y Y') (p : SuperExactPairing K X Y') :
    SuperExactPairing K X Y := by
  letI : ExactPairing (evenObj K C X) (evenObj K C Y') :=
    p.toEven
  exact ofEven
    (exactPairingCongrRight
      (evenSubcategoryIsoOfEvenIso e))

/-- Transport both objects of a super exact pairing across even
isomorphisms. -/
def congr
    (e : EvenIso K X X') (f : EvenIso K Y Y')
    (p : SuperExactPairing K X' Y') :
    SuperExactPairing K X Y := by
  letI : ExactPairing (evenObj K C X') (evenObj K C Y') :=
    p.toEven
  exact ofEven
    (exactPairingCongr
      (evenSubcategoryIsoOfEvenIso e)
      (evenSubcategoryIsoOfEvenIso f))

end SuperExactPairing

end Monoidal

end Superfusion.Category
