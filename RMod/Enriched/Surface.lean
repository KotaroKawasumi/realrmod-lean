import RMod.Enriched.Product

/-! The fixed abstract enriched interface, implemented independently of Challenge. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂ v w
namespace RMod
universe u₃ u₄

/-! A dedicated carrier synonym avoids assigning tensor enrichment to an ordinary product.
Mathlib supplies tensorμ, including the ambient braiding, but no tensor-product enrichment. -/
@[nolint unusedArguments]
def EnrichedTensorProduct (_V : Type v) (C : Type u₁) (D : Type u₂) := C × D

def EnrichedTensorProduct.of (V : Type v) {C : Type u₁} {D : Type u₂}
    (X : C) (Y : D) : EnrichedTensorProduct V C D :=
  show EnrichedTensorProduct V C D from (X, Y)

section EnrichedTensorProduct
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  (C : Type u₁) (D : Type u₂) [EnrichedCategory V C] [EnrichedCategory V D]

instance enrichedTensorProductEnriched (V : Type v) [Category.{w} V] [MonoidalCategory V]
    [BraidedCategory V] (C : Type u₁) (D : Type u₂)
    [EnrichedCategory V C] [EnrichedCategory V D] :
    EnrichedCategory V (EnrichedTensorProduct V C D) :=
  EnrichedSupport.productEnrichment V C D

/-- Fix Hom, identity and composition, including the precise braided interchange map. -/
theorem enrichedTensorProductEnriched_data :
    let E := enrichedTensorProductEnriched V C D
    (∀ X Y, E.Hom X Y = (X.1 ⟶[V] Y.1) ⊗ (X.2 ⟶[V] Y.2)) ∧
    (∀ X, HEq (E.id X) ((λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2))) ∧
    (∀ X Y Z, HEq (E.comp X Y Z) (tensorμ _ _ _ _ ≫
        (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2))) := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

end EnrichedTensorProduct

section
/-- Tensor two enriched functors using the fixed product enrichment. -/
def tensorEnrichedFunctors.{uC, uD, vE, wE, uC', uD'}
    (V : Type vE) [Category.{wE} V] [MonoidalCategory V] [BraidedCategory V]
    {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
    [EnrichedCategory V C] [EnrichedCategory V D]
    [EnrichedCategory V C'] [EnrichedCategory V D'] (F : EnrichedFunctor V C C') (G : EnrichedFunctor V D D') :
    EnrichedFunctor V (EnrichedTensorProduct V C D) (EnrichedTensorProduct V C' D') where
  obj X := EnrichedTensorProduct.of V (F.obj X.1) (G.obj X.2)
  map X Y := F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫ (eId V X.1 ⊗ₘ eId V X.2)) ≫
      (F.map X.1 X.1 ⊗ₘ G.map X.2 X.2) = _
    rw [Category.assoc, tensorHom_comp_tensorHom, F.map_id, G.map_id]
    rfl
  map_comp X Y Z := by
    change (tensorμ _ _ _ _ ≫ (eComp V X.1 Y.1 Z.1 ⊗ₘ eComp V X.2 Y.2 Z.2)) ≫
      (F.map X.1 Z.1 ⊗ₘ G.map X.2 Z.2) =
      ((F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2) ⊗ₘ
        (F.map Y.1 Z.1 ⊗ₘ G.map Y.2 Z.2)) ≫ tensorμ _ _ _ _ ≫ _
    rw [Category.assoc, tensorHom_comp_tensorHom, F.map_comp, G.map_comp,
      tensorμ_natural_assoc, ← tensorHom_comp_tensorHom]
    rfl

theorem tensorEnrichedFunctors_data.{uC, uD, vE, wE, uC', uD'}
    (V : Type vE) [Category.{wE} V] [MonoidalCategory V] [BraidedCategory V]
    {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
    [EnrichedCategory V C] [EnrichedCategory V D]
    [EnrichedCategory V C'] [EnrichedCategory V D'] (F : EnrichedFunctor V C C') (G : EnrichedFunctor V D D') :
    let T := tensorEnrichedFunctors V F G
    (∀ X, T.obj X = EnrichedTensorProduct.of V (F.obj X.1) (G.obj X.2)) ∧
    (∀ X Y, HEq (T.map X Y) (F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2)) := by
  constructor <;> intros <;> rfl

end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]

/-- Change only the displayed objects of an enriched functor, along specified equalities. -/
def reobject (F : EnrichedFunctor V C D) (obj : C → D) (h : F.obj = obj) :
    EnrichedFunctor V C D where
  obj := obj
  map X Y := F.map X Y ≫ eqToHom (congrArg₂ (EnrichedCategory.Hom (V := V))
    (congrFun h X) (congrFun h Y))
  map_id X := by subst obj; simp
  map_comp X Y Z := by subst obj; simp

theorem reobject_data (F : EnrichedFunctor V C D) (obj : C → D) (h : F.obj = obj) :
    let F' := reobject V F obj h
    (∀ X, F'.obj X = obj X) ∧
    (∀ X Y, HEq (F'.map X Y)
      (F.map X Y ≫ eqToHom (congrArg₂ (EnrichedCategory.Hom (V := V))
        (congrFun h X) (congrFun h Y)))) := by
  constructor <;> intros <;> rfl

/-- The law of a graded transformation, with its components prescribed in advance. -/
def IsGradedNaturalApp (A : Center V) (F G : EnrichedFunctor V C D)
    (app : ∀ X, A.1 ⟶ F.obj X ⟶[V] G.obj X) : Prop :=
  ∀ X Y, (A.2.β (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ app Y) ≫ eComp V _ _ _ =
    (app X ⊗ₘ G.map X Y) ≫ eComp V _ _ _

end
section
/-- Reassociate enriched products using the associator of the enriching category. -/
def reassociate.{uC, uD, vE, wE, uE}
    (V : Type vE) [Category.{wE} V] [MonoidalCategory V] [BraidedCategory V]
    (C : Type uC) (D : Type uD) (E : Type uE)
    [EnrichedCategory V C] [EnrichedCategory V D] [EnrichedCategory V E] :
    EnrichedFunctor V (EnrichedTensorProduct V (EnrichedTensorProduct V C D) E)
      (EnrichedTensorProduct V C (EnrichedTensorProduct V D E)) where
  obj X := EnrichedTensorProduct.of V X.1.1 (EnrichedTensorProduct.of V X.1.2 X.2)
  map X Y := (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom
  map_id X := by
    change ((λ_ (𝟙_ V)).inv ≫
      (((λ_ (𝟙_ V)).inv ≫ (eId V X.1.1 ⊗ₘ eId V X.1.2)) ⊗ₘ eId V X.2)) ≫
      (α_ _ _ _).hom = (λ_ (𝟙_ V)).inv ≫
        (eId V X.1.1 ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (eId V X.1.2 ⊗ₘ eId V X.2)))
    simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    monoidal
  map_comp X Y Z := by
    change (tensorμ _ _ _ _ ≫
      ((tensorμ _ _ _ _ ≫ (eComp V X.1.1 Y.1.1 Z.1.1 ⊗ₘ eComp V X.1.2 Y.1.2 Z.1.2)) ⊗ₘ
        eComp V X.2 Y.2 Z.2)) ≫ (α_ _ _ _).hom =
      ((α_ _ _ _).hom ⊗ₘ (α_ _ _ _).hom) ≫ tensorμ _ _ _ _ ≫
        (eComp V X.1.1 Y.1.1 Z.1.1 ⊗ₘ
          (tensorμ _ _ _ _ ≫ (eComp V X.1.2 Y.1.2 Z.1.2 ⊗ₘ eComp V X.2 Y.2 Z.2)))
    have h := congrArg (fun k => k ≫
      (eComp V X.1.1 Y.1.1 Z.1.1 ⊗ₘ
        (eComp V X.1.2 Y.1.2 Z.1.2 ⊗ₘ eComp V X.2 Y.2 Z.2)))
      (associator_monoidal (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)
        (Y.1.1 ⟶[V] Z.1.1) (Y.1.2 ⟶[V] Z.1.2) (Y.2 ⟶[V] Z.2))
    simpa only [← associator_naturality, ← tensorHom_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, Category.id_comp,
      Category.assoc] using h

theorem reassociate_data.{uC, uD, vE, wE, uE}
    (V : Type vE) [Category.{wE} V] [MonoidalCategory V] [BraidedCategory V]
    (C : Type uC) (D : Type uD) (E : Type uE)
    [EnrichedCategory V C] [EnrichedCategory V D] [EnrichedCategory V E] :
    let A := reassociate V C D E
    (∀ X, A.obj X = EnrichedTensorProduct.of V X.1.1
        (EnrichedTensorProduct.of V X.1.2 X.2)) ∧
    (∀ X Y, HEq (A.map X Y)
        (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom) := by
  constructor <;> intros <;> rfl

end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C]

omit [BraidedCategory V] in
private theorem eId_mul (X : C) :
    (eId V X ⊗ₘ eId V X) ≫ eComp V X X X = (λ_ (𝟙_ V)).hom ≫ eId V X := by
  apply (cancel_epi (λ_ (𝟙_ V)).inv).1
  rw [Iso.inv_hom_id_assoc]
  have h := ForgetEnrichment.homTo_comp V
    (𝟙 (ForgetEnrichment.of V X)) (𝟙 (ForgetEnrichment.of V X))
  simpa only [Category.id_comp, ForgetEnrichment.homTo_id, ForgetEnrichment.to_of, Category.assoc] using h.symm

/-- Insert a fixed object and its enriched identity on the left. -/
def insertLeft (I : C) : EnrichedFunctor V C (EnrichedTensorProduct V C C) where
  obj X := EnrichedTensorProduct.of V I X
  map X Y := (λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 (X ⟶[V] Y))
  map_id X := by
    change eId V X ≫ (λ_ (X ⟶[V] X)).inv ≫ (eId V I ⊗ₘ 𝟙 _) =
      (λ_ (𝟙_ V)).inv ≫ (eId V I ⊗ₘ eId V X)
    rw [leftUnitor_inv_naturality_assoc, tensorHom_id, MonoidalCategory.tensorHom_def']
  map_comp X Y Z := by
    change eComp V X Y Z ≫ (λ_ (X ⟶[V] Z)).inv ≫ (eId V I ⊗ₘ 𝟙 _) =
      (((λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 _)) ⊗ₘ
        ((λ_ (Y ⟶[V] Z)).inv ≫ (eId V I ⊗ₘ 𝟙 _))) ≫ tensorμ _ _ _ _ ≫
          (eComp V I I I ⊗ₘ eComp V X Y Z)
    rw [← tensorHom_comp_tensorHom, Category.assoc, tensorμ_natural_assoc,
      tensorHom_comp_tensorHom, eId_mul]
    have h := congrArg (fun k =>
      ((λ_ (X ⟶[V] Y)).inv ⊗ₘ (λ_ (Y ⟶[V] Z)).inv) ≫ k)
      (leftUnitor_monoidal (X ⟶[V] Y) (Y ⟶[V] Z))
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id] at h
    have q := congrArg (fun k => k ≫ (λ_ ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z))).inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] at q
    simp only [MonoidalCategory.tensorHom_def,
      comp_whiskerRight, Category.assoc]
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, q]
    simp [MonoidalCategory.tensorHom_def, Category.assoc]

theorem insertLeft_data (I : C) :
    let L := insertLeft V I
    (∀ X, L.obj X = EnrichedTensorProduct.of V I X) ∧
    (∀ X Y, HEq (L.map X Y)
      ((λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 (X ⟶[V] Y)))) := by
  constructor <;> intros <;> rfl

end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C]
/-- Insert a fixed object and its enriched identity on the right. -/
def insertRight (I : C) : EnrichedFunctor V C (EnrichedTensorProduct V C C) where
  obj X := EnrichedTensorProduct.of V X I
  map X Y := (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 (X ⟶[V] Y) ⊗ₘ eId V I)
  map_id X := by
    change eId V X ≫ (ρ_ (X ⟶[V] X)).inv ≫ (𝟙 _ ⊗ₘ eId V I) =
      (λ_ (𝟙_ V)).inv ≫ (eId V X ⊗ₘ eId V I)
    rw [rightUnitor_inv_naturality_assoc, id_tensorHom, MonoidalCategory.tensorHom_def, unitors_inv_equal]
  map_comp X Y Z := by
    change eComp V X Y Z ≫ (ρ_ (X ⟶[V] Z)).inv ≫ (𝟙 _ ⊗ₘ eId V I) =
      (((ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ₘ eId V I)) ⊗ₘ
        ((ρ_ (Y ⟶[V] Z)).inv ≫ (𝟙 _ ⊗ₘ eId V I))) ≫ tensorμ _ _ _ _ ≫
          (eComp V X Y Z ⊗ₘ eComp V I I I)
    rw [← tensorHom_comp_tensorHom, Category.assoc, tensorμ_natural_assoc,
      tensorHom_comp_tensorHom, eId_mul]
    have h := congrArg (fun k =>
      ((ρ_ (X ⟶[V] Y)).inv ⊗ₘ (ρ_ (Y ⟶[V] Z)).inv) ≫ k)
      (rightUnitor_monoidal (X ⟶[V] Y) (Y ⟶[V] Z))
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id] at h
    have q := congrArg (fun k => k ≫ (ρ_ ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z))).inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] at q
    simp only [MonoidalCategory.tensorHom_def',
      whiskerLeft_comp, Category.assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, q]
    simp [MonoidalCategory.tensorHom_def', Category.assoc]

theorem insertRight_data (I : C) :
    let R := insertRight V I
    (∀ X, R.obj X = EnrichedTensorProduct.of V X I) ∧
    (∀ X Y, HEq (R.map X Y)
      ((ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 (X ⟶[V] Y) ⊗ₘ eId V I))) := by
  constructor <;> intros <;> rfl

end
/-! Ordinary monoidal structure is an independent parameter. Hom-object equations express
naturality on every enrichment degree, using Mathlib's canonical enriched ordinary structure
on ForgetEnrichment and its pre/postcomposition maps. -/
section MonoidalEnrichment
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]

/-- The enriched tensor has exactly the ordinary tensor's object operation. -/
def TensorObjectsAgree (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) : Prop :=
  ∀ X Y : ForgetEnrichment V C,
    ForgetEnrichment.of V (T.obj (EnrichedTensorProduct.of V X Y)) =
      (MonoidalCategory.tensor (ForgetEnrichment V C)).obj (X, Y)

/-- Transport only along the specified equality of tensor objects. -/
def enrichedTensorMap (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C)
    (h : TensorObjectsAgree V T) (X X' Y Y' : ForgetEnrichment V C) :
    (X ⟶[V] X') ⊗ (Y ⟶[V] Y') ⟶ ((X ⊗ Y) ⟶[V] (X' ⊗ Y')) :=
  eqToHom ((enrichedTensorProductEnriched_data V C C).1
    (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y')).symm ≫
  T.map (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y') ≫
    eqToHom (congrArg₂ (EnrichedCategory.Hom (V := V)) (h X Y) (h X' Y'))

/-- The tensor map is the specified enriched map with only its target objects transported. -/
theorem enrichedTensorMap_data (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C)
    (h : TensorObjectsAgree V T) (X X' Y Y' : ForgetEnrichment V C) :
    HEq (enrichedTensorMap V T h X X' Y Y')
      (T.map (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y') ≫
        eqToHom (congrArg₂ (EnrichedCategory.Hom (V := V)) (h X Y) (h X' Y'))) := by
  simp only [enrichedTensorMap, eqToHom_refl, Category.id_comp]
  rfl

end MonoidalEnrichment
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]
  (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) (h : TensorObjectsAgree V T)

/-- The binary tensor with exactly the ordinary tensor objects. -/
def alignedTensor : EnrichedFunctor V (EnrichedTensorProduct V C C) C :=
  reobject V T (MonoidalCategory.tensor (ForgetEnrichment V C)).obj
    (funext fun X => h X.1 X.2)

/-- Both bracketings are functors on the same left-associated enriched product. -/
def leftAssociatedTensor :
    EnrichedFunctor V (EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) C :=
  (tensorEnrichedFunctors V (alignedTensor V T h) (EnrichedFunctor.id V C)).comp V
    (alignedTensor V T h)
def rightAssociatedTensor :
    EnrichedFunctor V (EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) C :=
  ((reassociate V C C C).comp V
    (tensorEnrichedFunctors V (EnrichedFunctor.id V C) (alignedTensor V T h))).comp V
      (alignedTensor V T h)

def leftUnitTensor : EnrichedFunctor V C C :=
  (insertLeft V (C := C) (𝟙_ (ForgetEnrichment V C))).comp V (alignedTensor V T h)
def rightUnitTensor : EnrichedFunctor V C C :=
  (insertRight V (C := C) (𝟙_ (ForgetEnrichment V C))).comp V (alignedTensor V T h)

/-- Canonical components come only from the supplied ordinary monoidal structure. -/
def associatorApp (X : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    𝟙_ V ⟶ ((leftAssociatedTensor V T h).obj X ⟶[V] (rightAssociatedTensor V T h).obj X) := by
  simpa only [leftAssociatedTensor, rightAssociatedTensor, alignedTensor, MonoidalCategory.tensor_obj, EnrichedFunctor.comp,
    tensorEnrichedFunctors_data, reobject_data, reassociate_data, EnrichedFunctor.id, EnrichedTensorProduct.of, ForgetEnrichment.of, ForgetEnrichment.to] using
    (ForgetEnrichment.homTo V (α_ (ForgetEnrichment.of V X.1.1)
    (ForgetEnrichment.of V X.1.2) (ForgetEnrichment.of V X.2)).hom)

/-- Fix the component to the supplied ordinary monoidal structure. -/
theorem associatorApp_data (X : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    HEq (associatorApp V T h X) (ForgetEnrichment.homTo V
      (α_ (ForgetEnrichment.of V X.1.1) (ForgetEnrichment.of V X.1.2) (ForgetEnrichment.of V X.2)).hom) := HEq.rfl

def leftUnitorApp (X : C) : 𝟙_ V ⟶ ((leftUnitTensor V T h).obj X ⟶[V] X) := by
  simpa only [leftUnitTensor, alignedTensor, MonoidalCategory.tensor_obj, EnrichedFunctor.comp, insertLeft_data, reobject_data, EnrichedTensorProduct.of, ForgetEnrichment.of, ForgetEnrichment.to] using
    (ForgetEnrichment.homTo V (λ_ (ForgetEnrichment.of V X)).hom)

/-- Fix the component to the supplied ordinary monoidal structure. -/
theorem leftUnitorApp_data (X : C) :
    HEq (leftUnitorApp V T h X) (ForgetEnrichment.homTo V (λ_ (ForgetEnrichment.of V X)).hom) := HEq.rfl

def rightUnitorApp (X : C) : 𝟙_ V ⟶ ((rightUnitTensor V T h).obj X ⟶[V] X) := by
  simpa only [rightUnitTensor, alignedTensor, MonoidalCategory.tensor_obj, EnrichedFunctor.comp, insertRight_data, reobject_data, EnrichedTensorProduct.of, ForgetEnrichment.of, ForgetEnrichment.to] using
    (ForgetEnrichment.homTo V (ρ_ (ForgetEnrichment.of V X)).hom)

/-- Fix the component to the supplied ordinary monoidal structure. -/
theorem rightUnitorApp_data (X : C) :
    HEq (rightUnitorApp V T h X) (ForgetEnrichment.homTo V (ρ_ (ForgetEnrichment.of V X)).hom) := HEq.rfl

end
section MonoidalEnrichment
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]

/-- Enriched monoidal structure adds the tensor lift and full Hom-object naturality.
Pentagon, triangle and ordinary naturality are already supplied by MonoidalCategory.
Only naturality properties are added; the ordinary components are fixed. -/
class MonoidalEnrichedCategory (C : Type u) [EnrichedCategory V C]
    [MonoidalCategory (ForgetEnrichment V C)] where
  tensor : EnrichedFunctor V (EnrichedTensorProduct V C C) C
  tensor_objects : TensorObjectsAgree V tensor
  tensor_even : ∀ {X X' Y Y' : ForgetEnrichment V C} (f : X ⟶ X') (g : Y ⟶ Y'),
    (λ_ (𝟙_ V)).inv ≫ (ForgetEnrichment.homTo V f ⊗ₘ ForgetEnrichment.homTo V g) ≫
      enrichedTensorMap V tensor tensor_objects X X' Y Y' =
        ForgetEnrichment.homTo V (f ⊗ₘ g)
  associator_isGradedNatural :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (leftAssociatedTensor V tensor tensor_objects) (rightAssociatedTensor V tensor tensor_objects) (associatorApp V tensor tensor_objects)
  leftUnitor_isGradedNatural :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (leftUnitTensor V tensor tensor_objects) (EnrichedFunctor.id V C) (leftUnitorApp V tensor tensor_objects)
  rightUnitor_isGradedNatural :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (rightUnitTensor V tensor tensor_objects) (EnrichedFunctor.id V C) (rightUnitorApp V tensor tensor_objects)

end MonoidalEnrichment

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]

/-- An ordinary natural isomorphism with full degree-zero enriched naturality.
Its inverse components are already fixed by the ordinary isomorphism. -/
structure EnrichedNatIso₀ (F G : EnrichedFunctor V C D) where
  toNatIso : F.forget ≅ G.forget
  hom_naturality : IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V)) F G
    (fun X => ForgetEnrichment.homTo V (toNatIso.hom.app (ForgetEnrichment.of V X)))

/-- Enriched quasi-inverse data; no extra triangle hypothesis is imposed. -/
structure EnrichedEquivalence (C : Type u₁) (D : Type u₂)
    [EnrichedCategory V C] [EnrichedCategory V D] where
  functor : EnrichedFunctor V C D
  inverse : EnrichedFunctor V D C
  unitIso : EnrichedNatIso₀ V (EnrichedFunctor.id V C) (functor.comp V inverse)
  counitIso : EnrichedNatIso₀ V (inverse.comp V functor) (EnrichedFunctor.id V D)

end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]
  [MonoidalCategory (ForgetEnrichment V C)] [MonoidalCategory (ForgetEnrichment V D)]
  [MC : MonoidalEnrichedCategory V C] [MD : MonoidalEnrichedCategory V D]

/-- Display the enriched tensor at the ordinary tensor objects using tensor_objects alone. -/
def canonicalTensor (C : Type u) [EnrichedCategory V C]
    [MonoidalCategory (ForgetEnrichment V C)] [M : MonoidalEnrichedCategory V C] :
    EnrichedFunctor V (EnrichedTensorProduct V C C) C :=
  reobject V M.tensor (MonoidalCategory.tensor (ForgetEnrichment V C)).obj
    (funext fun X => M.tensor_objects X.1 X.2)

/-- The two functors compared by the existing ordinary tensorator. -/
def mapThenTensor (F : EnrichedFunctor V C D) :
    EnrichedFunctor V (EnrichedTensorProduct V C C) D :=
  (tensorEnrichedFunctors V F F).comp V (canonicalTensor V D)
def tensorThenMap (F : EnrichedFunctor V C D) :
    EnrichedFunctor V (EnrichedTensorProduct V C C) D :=
  (canonicalTensor V C).comp V F

def tensoratorApp (F : EnrichedFunctor V C D) (m : F.forget.CoreMonoidal)
    (X : EnrichedTensorProduct V C C) :
    𝟙_ V ⟶ ((mapThenTensor V F).obj X ⟶[V] (tensorThenMap V F).obj X) := by
  simpa only [mapThenTensor, tensorThenMap, canonicalTensor, MonoidalCategory.tensor_obj, EnrichedFunctor.comp, EnrichedFunctor.forget,
    tensorEnrichedFunctors_data, reobject_data, EnrichedTensorProduct.of, ForgetEnrichment.of, ForgetEnrichment.to] using
    (ForgetEnrichment.homTo V
    (m.μIso (ForgetEnrichment.of V X.1) (ForgetEnrichment.of V X.2)).hom)

/-- Fix the component to the supplied ordinary monoidal structure. -/
theorem tensoratorApp_data (F : EnrichedFunctor V C D) (m : F.forget.CoreMonoidal)
    (X : EnrichedTensorProduct V C C) :
    HEq (tensoratorApp V F m X)
      (ForgetEnrichment.homTo V (m.μIso (ForgetEnrichment.of V X.1) (ForgetEnrichment.of V X.2)).hom) := HEq.rfl

/-- Ordinary strong monoidal data plus full enriched naturality of its fixed tensorator. -/
structure MonoidalEnrichedFunctor (F : EnrichedFunctor V C D) where
  coreMonoidal : F.forget.CoreMonoidal
  tensorator_naturality : IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
    (mapThenTensor V F) (tensorThenMap V F) (tensoratorApp V F coreMonoidal)

end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  (C : Type u₁) (D : Type u₂) [EnrichedCategory V C] [EnrichedCategory V D]
  [MonoidalCategory (ForgetEnrichment V C)] [MonoidalCategory (ForgetEnrichment V D)]
  [MonoidalEnrichedCategory V C] [MonoidalEnrichedCategory V D]

/-- An enriched equivalence with a strong monoidal forward functor. -/
structure MonoidalEnrichedEquivalence extends EnrichedEquivalence V C D where
  monoidal : MonoidalEnrichedFunctor V functor

end

end RMod
