import RMod.BrundanEllis.StackingSemigroupalUnit
import Mathlib.CategoryTheory.Equivalence

/-! Composition of tensor comparisons before a unit is selected.
An essentially surjective functor with invertible binary comparisons
already sends the unit to an object isomorphic to the target unit. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
universe vA uA vB uB vD uD
variable {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
  {B : Type uB} [Category.{vB} B] [MonoidalCategory B]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- Essential surjectivity supplies the initial unit isomorphism for normalization. -/
def semigroupalUnitImageIso (F : A ⥤ D) [F.EssSurj]
    (μ : ∀ X Y, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)) : F.obj (𝟙_ A) ≅ 𝟙_ D :=
  (ρ_ (F.obj (𝟙_ A))).symm ≪≫
    tensorIso (Iso.refl _) (F.objObjPreimageIso (𝟙_ D)).symm ≪≫
    μ (𝟙_ A) (F.objPreimage (𝟙_ D)) ≪≫
    F.mapIso (λ_ (F.objPreimage (𝟙_ D))) ≪≫ F.objObjPreimageIso (𝟙_ D)

variable (F : A ⥤ B) (J : B ⥤ D) (M : F.CoreMonoidal)
  (ν : ∀ X Y, J.obj X ⊗ J.obj Y ⟶ J.obj (X ⊗ Y))

/-- The binary comparison for the actual composite functor. -/
def semigroupalCompositeTensor (X Y : A) :
    (F ⋙ J).obj X ⊗ (F ⋙ J).obj Y ⟶ (F ⋙ J).obj (X ⊗ Y) :=
  ν (F.obj X) (F.obj Y) ≫ J.map (M.μIso X Y).hom

variable
  (hnL : ∀ {X Y : B} (u : X ⟶ Y) (Z : B),
    J.map u ▷ J.obj Z ≫ ν Y Z = ν X Z ≫ J.map (u ▷ Z))
  (hnR : ∀ {X Y : B} (Z : B) (u : X ⟶ Y),
    J.obj Z ◁ J.map u ≫ ν Z Y = ν Z X ≫ J.map (Z ◁ u))
  (ha : ∀ X Y Z : B,
    ν X Y ▷ J.obj Z ≫ ν (X ⊗ Y) Z ≫ J.map (α_ X Y Z).hom =
      (α_ (J.obj X) (J.obj Y) (J.obj Z)).hom ≫ J.obj X ◁ ν Y Z ≫ ν X (Y ⊗ Z))

include hnL in
/-- Naturality in the first input passes to the composite comparison. -/
theorem semigroupalCompositeTensor_natural_left {X Y : A} (u : X ⟶ Y) (Z : A) :
    (F ⋙ J).map u ▷ (F ⋙ J).obj Z ≫ semigroupalCompositeTensor F J M ν Y Z =
      semigroupalCompositeTensor F J M ν X Z ≫ (F ⋙ J).map (u ▷ Z) := by
  dsimp only [semigroupalCompositeTensor, Functor.comp]
  rw [reassoc_of% (hnL (F.map u) (F.obj Z)), ← J.map_comp,
    M.μIso_hom_natural_left, J.map_comp, Category.assoc]

include hnR in
/-- Naturality in the second input passes to the composite comparison. -/
theorem semigroupalCompositeTensor_natural_right {X Y : A} (Z : A) (u : X ⟶ Y) :
    (F ⋙ J).obj Z ◁ (F ⋙ J).map u ≫ semigroupalCompositeTensor F J M ν Z Y =
      semigroupalCompositeTensor F J M ν Z X ≫ (F ⋙ J).map (Z ◁ u) := by
  dsimp only [semigroupalCompositeTensor, Functor.comp]
  rw [reassoc_of% (hnR (F.obj Z) (F.map u)), ← J.map_comp,
    M.μIso_hom_natural_right, J.map_comp, Category.assoc]

include hnL hnR ha in
/-- The composite retains associativity of both given binary comparisons. -/
theorem semigroupalCompositeTensor_associativity (X Y Z : A) :
    semigroupalCompositeTensor F J M ν X Y ▷ (F ⋙ J).obj Z ≫
      semigroupalCompositeTensor F J M ν (X ⊗ Y) Z ≫ (F ⋙ J).map (α_ X Y Z).hom =
    (α_ ((F ⋙ J).obj X) ((F ⋙ J).obj Y) ((F ⋙ J).obj Z)).hom ≫
      (F ⋙ J).obj X ◁ semigroupalCompositeTensor F J M ν Y Z ≫
      semigroupalCompositeTensor F J M ν X (Y ⊗ Z) := by
  dsimp only [semigroupalCompositeTensor, Functor.comp]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (hnL (M.μIso X Y).hom (F.obj Z)),
    ← J.map_comp, ← J.map_comp, M.associativity,
    J.map_comp, J.map_comp,
    reassoc_of% (ha (F.obj X) (F.obj Y) (F.obj Z)),
    ← reassoc_of% (hnR (F.obj X) (M.μIso Y Z).hom)]

include hnL hnR ha in
/-- Invertibility only on the image of F suffices for the composite to be strong monoidal. -/
def coreMonoidalOfSupportedComposite [(F ⋙ J).EssSurj]
    (N : ∀ X Y : A, J.obj (F.obj X) ⊗ J.obj (F.obj Y) ≅ J.obj (F.obj X ⊗ F.obj Y))
    (hN : ∀ X Y, (N X Y).hom = ν (F.obj X) (F.obj Y)) : (F ⋙ J).CoreMonoidal := by
  let μ : ∀ X Y : A, (F ⋙ J).obj X ⊗ (F ⋙ J).obj Y ≅ (F ⋙ J).obj (X ⊗ Y) :=
    fun X Y => N X Y ≪≫ J.mapIso (M.μIso X Y)
  have hμ : ∀ X Y, (μ X Y).hom = semigroupalCompositeTensor F J M ν X Y := by
    intro X Y
    exact congrArg (fun u => u ≫ J.map (M.μIso X Y).hom) (hN X Y)
  apply coreMonoidalOfAssociativity (F ⋙ J) μ (semigroupalUnitImageIso (F ⋙ J) μ)
  · intro X Y u Z
    rw [hμ, hμ]
    exact semigroupalCompositeTensor_natural_left F J M ν hnL u Z
  · intro X Y Z u
    rw [hμ, hμ]
    exact semigroupalCompositeTensor_natural_right F J M ν hnR Z u
  · intro X Y Z
    rw [hμ, hμ, hμ, hμ]
    exact semigroupalCompositeTensor_associativity F J M ν hnL hnR ha X Y Z

/-- Unit normalization retains the specified composite binary map. -/
theorem coreMonoidalOfSupportedComposite_tensor [(F ⋙ J).EssSurj]
    (N : ∀ X Y : A, J.obj (F.obj X) ⊗ J.obj (F.obj Y) ≅ J.obj (F.obj X ⊗ F.obj Y))
    (hN : ∀ X Y, (N X Y).hom = ν (F.obj X) (F.obj Y)) (X Y : A) :
    ((coreMonoidalOfSupportedComposite F J M ν hnL hnR ha N hN).μIso X Y).hom =
      ν (F.obj X) (F.obj Y) ≫ J.map (M.μIso X Y).hom := by
  exact congrArg (fun u => u ≫ J.map (M.μIso X Y).hom) (hN X Y)

end RMod.BrundanEllis.Stacking
