import RMod.Enriched.SuperSurface

/-! Proven transport, coherence, and equivalence APIs for the independent Solution. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂ v w
/-! Solution-side transport and compatibility proofs. The regression runners check these
against the opaque Challenge definitions and their registered exact-data contracts.
No proof implementation imports Challenge. -/
namespace RMod
universe u₃ u₄
/-! Pointwise transport of the registered exact-data equations. -/
section
variable {A : Sort u} {B : A → A → Sort v}
theorem heq_congr₂ (f : ∀ x y, B x y) {x x' y y' : A} (hx : x = x') (hy : y = y') :
    HEq (f x y) (f x' y') := by subst x'; subst y'; rfl
end
section
variable {V : Type v} [Category.{w} V]
theorem comp_heq {X Y Z X' Y' Z' : V} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst X'; subst Y'; subst Z'; cases hf; cases hg; rfl

theorem eqToHom_comp_heq {X X' Y : V} (h : X = X') (f : X' ⟶ Y) :
    HEq (eqToHom h ≫ f) f := by subst X'; simp
end
section
variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
theorem tensorHom_heq {X Y Z W X' Y' Z' W' : V}
    (hx : X = X') (hy : Y = Y') (hz : Z = Z') (hw : W = W')
    {f : X ⟶ Y} {g : Z ⟶ W} {f' : X' ⟶ Y'} {g' : Z' ⟶ W'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ⊗ₘ g) (f' ⊗ₘ g') := by
  subst X'; subst Y'; subst Z'; subst W'; cases hf; cases hg; rfl
end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]
  {C' : Type u₃} {D' : Type u₄} [EnrichedCategory V C'] [EnrichedCategory V D']

theorem tensorEnrichedFunctors_map_heq (F : EnrichedFunctor V C C') (G : EnrichedFunctor V D D')
    (X Y : EnrichedTensorProduct V C D) :
    HEq ((tensorEnrichedFunctors V F G).map X Y) (F.map X.1 Y.1 ⊗ₘ G.map X.2 Y.2) := by
  exact (tensorEnrichedFunctors_data V F G).2 X Y

theorem reobject_map_heq (F : EnrichedFunctor V C D) (obj : C → D) (h : F.obj = obj) (X Y : C) :
    HEq ((reobject V F obj h).map X Y)
      (F.map X Y ≫ eqToHom (congrArg₂ (EnrichedCategory.Hom (V := V)) (congrFun h X) (congrFun h Y))) := by
  exact (reobject_data V F obj h).2 X Y
end

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C]

theorem insertLeft_map_heq (I X Y : C) :
    HEq ((insertLeft V I).map X Y) ((λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 (X ⟶[V] Y))) := by
  exact (insertLeft_data V I).2 X Y

theorem insertRight_map_heq (I X Y : C) :
    HEq ((insertRight V I).map X Y) ((ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 (X ⟶[V] Y) ⊗ₘ eId V I)) := by
  exact (insertRight_data V I).2 X Y

theorem reassociate_map_heq (X Y : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    HEq ((reassociate V C C C).map X Y)
      (α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom := by
  exact (reassociate_data V C C C).2 X Y

variable [MonoidalCategory (ForgetEnrichment V C)]
  (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) (h : TensorObjectsAgree V T)

theorem alignedTensor_map_heq (X Y : EnrichedTensorProduct V C C) :
    HEq ((alignedTensor V T h).map X Y) (enrichedTensorMap V T h X.1 Y.1 X.2 Y.2) := by
  exact (reobject_map_heq V T _ _ X Y).trans
    (enrichedTensorMap_data V T h X.1 Y.1 X.2 Y.2).symm

theorem alignedTensor_map_heq_of_eq {X Y X' Y' : EnrichedTensorProduct V C C}
    (hx : X = X') (hy : Y = Y') :
    HEq ((alignedTensor V T h).map X Y) (enrichedTensorMap V T h X'.1 Y'.1 X'.2 Y'.2) :=
  (alignedTensor_map_heq V T h X Y).trans
    (heq_congr₂ (fun P Q : EnrichedTensorProduct V C C =>
      enrichedTensorMap V T h P.1 Q.1 P.2 Q.2) hx hy)

theorem leftUnitTensor_map_heq (X Y : C) :
    HEq ((leftUnitTensor V T h).map X Y)
      (((λ_ (X ⟶[V] Y)).inv ≫ (eId V (𝟙_ (ForgetEnrichment V C)) ⊗ₘ 𝟙 (X ⟶[V] Y))) ≫
        enrichedTensorMap V T h (𝟙_ _) (𝟙_ _) X Y) := by
  unfold leftUnitTensor EnrichedFunctor.comp
  refine comp_heq rfl ?_ ?_ (insertLeft_map_heq V _ X Y) ?_
  · simp only [insertLeft_data, enrichedTensorProductEnriched_data, EnrichedTensorProduct.of]
  · simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertLeft_data, EnrichedTensorProduct.of]
  · apply alignedTensor_map_heq_of_eq V T h (X' := (EnrichedTensorProduct.of V (𝟙_ (ForgetEnrichment V C)) X)) (Y' := (EnrichedTensorProduct.of V (𝟙_ (ForgetEnrichment V C)) Y))
    all_goals simp only [insertLeft_data, EnrichedTensorProduct.of]


theorem rightUnitTensor_map_heq (X Y : C) :
    HEq ((rightUnitTensor V T h).map X Y)
      (((ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 (X ⟶[V] Y) ⊗ₘ eId V (𝟙_ (ForgetEnrichment V C)))) ≫
        enrichedTensorMap V T h X Y (𝟙_ _) (𝟙_ _)) := by
  unfold rightUnitTensor EnrichedFunctor.comp
  refine comp_heq rfl ?_ ?_ (insertRight_map_heq V _ X Y) ?_
  · simp only [insertRight_data, enrichedTensorProductEnriched_data, EnrichedTensorProduct.of]
  · simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertRight_data, EnrichedTensorProduct.of]
  · apply alignedTensor_map_heq_of_eq V T h (X' := (EnrichedTensorProduct.of V X (𝟙_ (ForgetEnrichment V C)))) (Y' := (EnrichedTensorProduct.of V Y (𝟙_ (ForgetEnrichment V C))))
    all_goals simp only [insertRight_data, EnrichedTensorProduct.of]


theorem leftAssociatedTensor_map_heq
    (X Y : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    HEq ((leftAssociatedTensor V T h).map X Y)
      ((enrichedTensorMap V T h X.1.1 Y.1.1 X.1.2 Y.1.2 ⊗ₘ 𝟙 (X.2 ⟶[V] Y.2)) ≫
        enrichedTensorMap V T h (X.1.1 ⊗ X.1.2) (Y.1.1 ⊗ Y.1.2) X.2 Y.2) := by
  unfold leftAssociatedTensor EnrichedFunctor.comp
  refine comp_heq ?_ ?_ ?_ ?_ ?_
  · simp only [enrichedTensorProductEnriched_data]
  · simp only [tensorEnrichedFunctors_data, enrichedTensorProductEnriched_data,
      alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id]
  · simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data, tensorEnrichedFunctors_data,
      EnrichedTensorProduct.of, EnrichedFunctor.id]
  · apply (tensorEnrichedFunctors_map_heq V _ _ X Y).trans
    exact tensorHom_heq (by simp only [enrichedTensorProductEnriched_data])
      (by simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data]) rfl rfl
      (alignedTensor_map_heq V T h X.1 Y.1) HEq.rfl
  · apply alignedTensor_map_heq_of_eq V T h (X' := (EnrichedTensorProduct.of V (tensorObj (C := ForgetEnrichment V C) X.1.1 X.1.2) X.2)) (Y' := (EnrichedTensorProduct.of V (tensorObj (C := ForgetEnrichment V C) Y.1.1 Y.1.2) Y.2))
    all_goals simp only [tensorEnrichedFunctors_data, alignedTensor, MonoidalCategory.tensor_obj, reobject_data,
      EnrichedTensorProduct.of, EnrichedFunctor.id]


theorem tensorRight_map_heq (X Y : EnrichedTensorProduct V C (EnrichedTensorProduct V C C)) :
    HEq ((tensorEnrichedFunctors V (EnrichedFunctor.id V C) (alignedTensor V T h)).map X Y)
      (𝟙 (X.1 ⟶[V] Y.1) ⊗ₘ enrichedTensorMap V T h X.2.1 Y.2.1 X.2.2 Y.2.2) := by
  apply (tensorEnrichedFunctors_map_heq V _ _ X Y).trans
  exact tensorHom_heq rfl rfl (by simp only [enrichedTensorProductEnriched_data])
    (by simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data]) HEq.rfl (alignedTensor_map_heq V T h X.2 Y.2)

theorem tensorRight_map_heq_of_eq
    {X Y X' Y' : EnrichedTensorProduct V C (EnrichedTensorProduct V C C)}
    (hx : X = X') (hy : Y = Y') :
    HEq ((tensorEnrichedFunctors V (EnrichedFunctor.id V C) (alignedTensor V T h)).map X Y)
      (𝟙 (X'.1 ⟶[V] Y'.1) ⊗ₘ enrichedTensorMap V T h X'.2.1 Y'.2.1 X'.2.2 Y'.2.2) :=
  (tensorRight_map_heq V T h X Y).trans
    (heq_congr₂ (fun P Q : EnrichedTensorProduct V C (EnrichedTensorProduct V C C) =>
      𝟙 (P.1 ⟶[V] Q.1) ⊗ₘ enrichedTensorMap V T h P.2.1 Q.2.1 P.2.2 Q.2.2) hx hy)

theorem rightAssociatedTensor_map_heq
    (X Y : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    HEq ((rightAssociatedTensor V T h).map X Y)
      (((α_ (X.1.1 ⟶[V] Y.1.1) (X.1.2 ⟶[V] Y.1.2) (X.2 ⟶[V] Y.2)).hom ≫
        (𝟙 (X.1.1 ⟶[V] Y.1.1) ⊗ₘ enrichedTensorMap V T h X.1.2 Y.1.2 X.2 Y.2)) ≫
        enrichedTensorMap V T h X.1.1 Y.1.1 (X.1.2 ⊗ X.2) (Y.1.2 ⊗ Y.2)) := by
  unfold rightAssociatedTensor EnrichedFunctor.comp
  refine comp_heq ?_ ?_ ?_ ?_ ?_
  · simp only [enrichedTensorProductEnriched_data]
  · simp only [tensorEnrichedFunctors_data, reassociate_data, enrichedTensorProductEnriched_data,
      alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id]
  · simp only [alignedTensor, MonoidalCategory.tensor_obj, reobject_data, tensorEnrichedFunctors_data, reassociate_data,
      EnrichedTensorProduct.of, EnrichedFunctor.id]
  · refine comp_heq ?_ ?_ ?_ (reassociate_map_heq V X Y) ?_
    · simp only [enrichedTensorProductEnriched_data]
    · simp only [reassociate_data, enrichedTensorProductEnriched_data, EnrichedTensorProduct.of]
    · simp only [tensorEnrichedFunctors_data, reassociate_data, enrichedTensorProductEnriched_data,
        alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id]
    · apply tensorRight_map_heq_of_eq V T h
        (X' := EnrichedTensorProduct.of V X.1.1 (EnrichedTensorProduct.of V X.1.2 X.2))
        (Y' := EnrichedTensorProduct.of V Y.1.1 (EnrichedTensorProduct.of V Y.1.2 Y.2))
      all_goals simp only [reassociate_data, EnrichedTensorProduct.of]
  · apply alignedTensor_map_heq_of_eq V T h (X' := (EnrichedTensorProduct.of V X.1.1 (tensorObj (C := ForgetEnrichment V C) X.1.2 X.2))) (Y' := (EnrichedTensorProduct.of V Y.1.1 (tensorObj (C := ForgetEnrichment V C) Y.1.2 Y.2)))
    all_goals simp only [tensorEnrichedFunctors_data, reassociate_data, alignedTensor, MonoidalCategory.tensor_obj,
      reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id]

end
end RMod
namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]
set_option backward.isDefEq.respectTransparency false in
theorem degreeZero_naturality_iff (F G : EnrichedFunctor V C D)
    (app : ∀ X, 𝟙_ V ⟶ F.obj X ⟶[V] G.obj X) :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V)) F G app ↔
    ∀ X Y, F.map X Y ≫ eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X))
        (ForgetEnrichment.homOf V (app Y)) =
      G.map X Y ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V (app X))
        (ForgetEnrichment.of V (G.obj Y)) := by
  apply forall_congr'; intro X
  apply forall_congr'; intro Y
  change (β_ (𝟙_ V) (X ⟶[V] Y)).hom ≫ (F.map X Y ⊗ₘ app Y) ≫ eComp V _ _ _ =
    (app X ⊗ₘ G.map X Y) ≫ eComp V _ _ _ ↔ _
  rw [← cancel_epi (λ_ (X ⟶[V] Y)).inv]
  rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id_assoc]
  rw [MonoidalCategory.tensorHom_def (F.map X Y) (app Y), MonoidalCategory.tensorHom_def' (app X) (G.map X Y)]
  simp only [eHomWhiskerLeft, eHomWhiskerRight, Category.assoc,
    ← rightUnitor_inv_naturality_assoc, ← leftUnitor_inv_naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Full naturality of the inverse follows from the hom and the component inverse laws. -/
theorem EnrichedNatIso₀.inv_naturality {F G : EnrichedFunctor V C D} (e : EnrichedNatIso₀ V F G) :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V)) G F
      (fun X => ForgetEnrichment.homTo V (e.toNatIso.inv.app (ForgetEnrichment.of V X))) := by
  rw [degreeZero_naturality_iff]
  intro X Y
  have h := (degreeZero_naturality_iff V F G _).1 e.hom_naturality X Y
  have q := congrArg (fun k => k ≫
    eHomWhiskerLeft V (F.forget.obj (ForgetEnrichment.of V X))
      (e.toNatIso.inv.app (ForgetEnrichment.of V Y)) ≫
    eHomWhiskerRight V (e.toNatIso.inv.app (ForgetEnrichment.of V X))
      (F.forget.obj (ForgetEnrichment.of V Y))) h
  have hid (A B : ForgetEnrichment V D) : eHomWhiskerLeft V A (𝟙 B) = 𝟙 _ := by
    simp only [eHomWhiskerLeft, eHomEquiv_id, e_comp_id]
  dsimp only [EnrichedFunctor.forget] at q
  simp only [ForgetEnrichment.homOf_homTo, ForgetEnrichment.to_of, Category.assoc,
    ← eHom_whisker_exchange_assoc, ← eHomWhiskerLeft_comp_assoc,
    ← eHomWhiskerRight_comp (C := ForgetEnrichment V D) V,
    Iso.hom_inv_id_app, Iso.inv_hom_id_app,
    eHomWhiskerRight_id (C := ForgetEnrichment V D) V, Category.comp_id] at q ⊢
  rw [hid (ForgetEnrichment.of V (F.obj X)) (ForgetEnrichment.of V (F.obj Y))] at q
  erw [Category.id_comp] at q
  exact q.symm

end
end RMod
namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V]
  {C : Type u} [EnrichedCategory V C]

theorem naturality_transport_iff {H H' : V} {A B A₁ B₁ A' B' A₁' B₁' : C}
    (hH : H = H') (hA : A = A') (hB : B = B') (hA₁ : A₁ = A₁') (hB₁ : B₁ = B₁')
    {f : H ⟶ A ⟶[V] B} {g : H ⟶ A₁ ⟶[V] B₁}
    {a : 𝟙_ V ⟶ A ⟶[V] A₁} {b : 𝟙_ V ⟶ B ⟶[V] B₁}
    {f' : H' ⟶ A' ⟶[V] B'} {g' : H' ⟶ A₁' ⟶[V] B₁'}
    {a' : 𝟙_ V ⟶ A' ⟶[V] A₁'} {b' : 𝟙_ V ⟶ B' ⟶[V] B₁'}
    (hf : HEq f f') (hg : HEq g g') (ha : HEq a a') (hb : HEq b b') :
    (f ≫ eHomWhiskerLeft V (ForgetEnrichment.of V A) (ForgetEnrichment.homOf V b) =
      g ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V a) (ForgetEnrichment.of V B₁)) ↔
    (f' ≫ eHomWhiskerLeft V (ForgetEnrichment.of V A') (ForgetEnrichment.homOf V b') =
      g' ≫ eHomWhiskerRight V (ForgetEnrichment.homOf V a') (ForgetEnrichment.of V B₁')) := by
  subst H'; subst A'; subst B'; subst A₁'; subst B₁'
  cases hf; cases hg; cases ha; cases hb
  rfl
end
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]
  (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) (h : TensorObjectsAgree V T)

theorem leftUnitorApp_heq (X : C) :
    HEq (leftUnitorApp V T h X) (ForgetEnrichment.homTo V (λ_ (ForgetEnrichment.of V X)).hom) := by
  exact leftUnitorApp_data V T h X

theorem rightUnitorApp_heq (X : C) :
    HEq (rightUnitorApp V T h X) (ForgetEnrichment.homTo V (ρ_ (ForgetEnrichment.of V X)).hom) := by
  exact rightUnitorApp_data V T h X

theorem associatorApp_heq (X : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :
    HEq (associatorApp V T h X) (ForgetEnrichment.homTo V
      (α_ (ForgetEnrichment.of V X.1.1) (ForgetEnrichment.of V X.1.2) (ForgetEnrichment.of V X.2)).hom) := by
  exact associatorApp_data V T h X

end
end RMod
namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]
  (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) (h : TensorObjectsAgree V T)
theorem leftUnitor_isGradedNatural_iff :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (leftUnitTensor V T h) (EnrichedFunctor.id V C) (leftUnitorApp V T h) ↔
    ∀ X Y : ForgetEnrichment V C,
    (λ_ (X ⟶[V] Y)).inv ≫
      (eId V (𝟙_ (ForgetEnrichment V C)) ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
      enrichedTensorMap V T h (𝟙_ _) (𝟙_ _) X Y ≫
      eHomWhiskerLeft V ((𝟙_ _) ⊗ X) (λ_ Y).hom =
    eHomWhiskerRight V (λ_ X).hom Y := by
  rw [degreeZero_naturality_iff]
  apply forall_congr' fun X => forall_congr' fun Y => ?_
  simpa only [Category.assoc, Category.id_comp, ForgetEnrichment.homOf_homTo, EnrichedFunctor.id,
    ForgetEnrichment.of] using
    (naturality_transport_iff V rfl
      (by simp only [leftUnitTensor, EnrichedFunctor.comp, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertLeft_data, EnrichedTensorProduct.of])
      (by simp only [leftUnitTensor, EnrichedFunctor.comp, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertLeft_data, EnrichedTensorProduct.of]) rfl rfl
      (leftUnitTensor_map_heq V T h X Y) (HEq.rfl (a := 𝟙 (X ⟶[V] Y)))
      (leftUnitorApp_heq V T h X) (leftUnitorApp_heq V T h Y))


theorem rightUnitor_isGradedNatural_iff :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (rightUnitTensor V T h) (EnrichedFunctor.id V C) (rightUnitorApp V T h) ↔
    ∀ X Y : ForgetEnrichment V C,
    (ρ_ (X ⟶[V] Y)).inv ≫
      (𝟙 (X ⟶[V] Y) ⊗ₘ eId V (𝟙_ (ForgetEnrichment V C))) ≫
      enrichedTensorMap V T h X Y (𝟙_ _) (𝟙_ _) ≫
      eHomWhiskerLeft V (X ⊗ (𝟙_ _)) (ρ_ Y).hom =
    eHomWhiskerRight V (ρ_ X).hom Y := by
  rw [degreeZero_naturality_iff]
  apply forall_congr' fun X => forall_congr' fun Y => ?_
  simpa only [Category.assoc, Category.id_comp, ForgetEnrichment.homOf_homTo, EnrichedFunctor.id,
    ForgetEnrichment.of] using
    (naturality_transport_iff V rfl
      (by simp only [rightUnitTensor, EnrichedFunctor.comp, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertRight_data, EnrichedTensorProduct.of])
      (by simp only [rightUnitTensor, EnrichedFunctor.comp, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, insertRight_data, EnrichedTensorProduct.of]) rfl rfl
      (rightUnitTensor_map_heq V T h X Y) (HEq.rfl (a := 𝟙 (X ⟶[V] Y)))
      (rightUnitorApp_heq V T h X) (rightUnitorApp_heq V T h Y))

end
end RMod
namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]
  (T : EnrichedFunctor V (EnrichedTensorProduct V C C) C) (h : TensorObjectsAgree V T)
theorem associator_isGradedNatural_iff :
    IsGradedNaturalApp V ((Center.ofBraided V).obj (𝟙_ V))
      (leftAssociatedTensor V T h) (rightAssociatedTensor V T h) (associatorApp V T h) ↔
    ∀ X X' Y Y' Z Z' : ForgetEnrichment V C,
      (enrichedTensorMap V T h X X' Y Y' ⊗ₘ 𝟙 (Z ⟶[V] Z')) ≫
        enrichedTensorMap V T h (X ⊗ Y) (X' ⊗ Y') Z Z' ≫
        eHomWhiskerLeft V ((X ⊗ Y) ⊗ Z) (α_ X' Y' Z').hom =
      (α_ (X ⟶[V] X') (Y ⟶[V] Y') (Z ⟶[V] Z')).hom ≫
        (𝟙 (X ⟶[V] X') ⊗ₘ enrichedTensorMap V T h Y Y' Z Z') ≫
        enrichedTensorMap V T h X X' (Y ⊗ Z) (Y' ⊗ Z') ≫
        eHomWhiskerRight V (α_ X Y Z).hom (X' ⊗ (Y' ⊗ Z')) := by
  have ht (X Y : EnrichedTensorProduct V (EnrichedTensorProduct V C C) C) :=
    naturality_transport_iff V
      (by simp only [enrichedTensorProductEnriched_data])
      (by simp only [leftAssociatedTensor, EnrichedFunctor.comp, tensorEnrichedFunctors_data,
        alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id])
      (by simp only [leftAssociatedTensor, EnrichedFunctor.comp, tensorEnrichedFunctors_data,
        alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id])
      (by simp only [rightAssociatedTensor, EnrichedFunctor.comp, tensorEnrichedFunctors_data,
        reassociate_data, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id])
      (by simp only [rightAssociatedTensor, EnrichedFunctor.comp, tensorEnrichedFunctors_data,
        reassociate_data, alignedTensor, MonoidalCategory.tensor_obj, reobject_data, EnrichedTensorProduct.of, EnrichedFunctor.id])
      (leftAssociatedTensor_map_heq V T h X Y) (rightAssociatedTensor_map_heq V T h X Y)
      (associatorApp_heq V T h X) (associatorApp_heq V T h Y)
  rw [degreeZero_naturality_iff]
  constructor
  · intro hn X X' Y Y' Z Z'
    simpa only [Category.assoc, ForgetEnrichment.homOf_homTo, ForgetEnrichment.of,
      EnrichedTensorProduct.of] using
      (ht (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X Y) Z)
        (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X' Y') Z')).mp
          (hn (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X Y) Z)
            (EnrichedTensorProduct.of V (EnrichedTensorProduct.of V X' Y') Z'))
  · intro hn X Y
    apply (ht X Y).mpr
    simpa only [Category.assoc, ForgetEnrichment.homOf_homTo, ForgetEnrichment.of] using
      hn X.1.1 Y.1.1 X.1.2 Y.1.2 X.2 Y.2
end
end RMod
namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]
  [MonoidalCategory (ForgetEnrichment V C)] [MonoidalCategory (ForgetEnrichment V D)]
  [MC : MonoidalEnrichedCategory V C] [MD : MonoidalEnrichedCategory V D]

omit [MonoidalCategory (ForgetEnrichment V C)] MC in
theorem mapThenTensor_map_heq (F : EnrichedFunctor V C D) (X Y : EnrichedTensorProduct V C C) :
    HEq ((mapThenTensor V F).map X Y)
      ((F.map X.1 Y.1 ⊗ₘ F.map X.2 Y.2) ≫
        enrichedTensorMap V MD.tensor MD.tensor_objects (F.obj X.1) (F.obj Y.1) (F.obj X.2) (F.obj Y.2)) := by
  unfold mapThenTensor EnrichedFunctor.comp
  refine comp_heq ?_ ?_ ?_ (tensorEnrichedFunctors_map_heq V F F X Y) ?_
  · simp only [enrichedTensorProductEnriched_data]
  · simp only [tensorEnrichedFunctors_data, enrichedTensorProductEnriched_data, EnrichedTensorProduct.of]
  · simp only [canonicalTensor, MonoidalCategory.tensor_obj, reobject_data, tensorEnrichedFunctors_data, EnrichedTensorProduct.of]
  · apply alignedTensor_map_heq_of_eq V MD.tensor MD.tensor_objects
      (X' := EnrichedTensorProduct.of V (F.obj X.1) (F.obj X.2))
      (Y' := EnrichedTensorProduct.of V (F.obj Y.1) (F.obj Y.2))
    all_goals simp only [tensorEnrichedFunctors_data]

omit [MonoidalCategory (ForgetEnrichment V D)] MD in
theorem tensorThenMap_map_heq (F : EnrichedFunctor V C D) (X Y : EnrichedTensorProduct V C C) :
    HEq ((tensorThenMap V F).map X Y)
      (enrichedTensorMap V MC.tensor MC.tensor_objects X.1 Y.1 X.2 Y.2 ≫
        F.map (tensorObj (C := ForgetEnrichment V C) X.1 X.2) (tensorObj (C := ForgetEnrichment V C) Y.1 Y.2)) := by
  unfold tensorThenMap EnrichedFunctor.comp
  refine comp_heq ?_ ?_ ?_ (alignedTensor_map_heq V MC.tensor MC.tensor_objects X Y) ?_
  · simp only [enrichedTensorProductEnriched_data]
  · simp only [canonicalTensor, MonoidalCategory.tensor_obj, reobject_data]
  · simp only [canonicalTensor, MonoidalCategory.tensor_obj, reobject_data]
  · apply heq_congr₂ F.map
    all_goals simp only [canonicalTensor, MonoidalCategory.tensor_obj, reobject_data]

theorem tensoratorApp_heq (F : EnrichedFunctor V C D) (m : F.forget.CoreMonoidal)
    (X : EnrichedTensorProduct V C C) :
    HEq (tensoratorApp V F m X)
      (ForgetEnrichment.homTo V (m.μIso (ForgetEnrichment.of V X.1) (ForgetEnrichment.of V X.2)).hom) := by
  exact tensoratorApp_data V F m X

/-- Full tensorator naturality in the original Hom-object coordinates. -/
theorem MonoidalEnrichedFunctor.tensor_naturality {F : EnrichedFunctor V C D}
    (m : MonoidalEnrichedFunctor V F) (X X' Y Y' : ForgetEnrichment V C) :
    (F.map X X' ⊗ₘ F.map Y Y') ≫
      enrichedTensorMap V MD.tensor MD.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y') ≫
      eHomWhiskerLeft V (ForgetEnrichment.of V (F.obj X) ⊗ ForgetEnrichment.of V (F.obj Y)) (m.coreMonoidal.μIso X' Y').hom =
    enrichedTensorMap V MC.tensor MC.tensor_objects X X' Y Y' ≫ F.map (tensorObj (C := ForgetEnrichment V C) X Y) (tensorObj (C := ForgetEnrichment V C) X' Y') ≫
      eHomWhiskerRight V (m.coreMonoidal.μIso X Y).hom (F.forget.obj (X' ⊗ Y')) := by
  have hn := (degreeZero_naturality_iff V _ _ _).1 m.tensorator_naturality
    (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y')
  have ht := naturality_transport_iff V
    (by simp only [enrichedTensorProductEnriched_data, EnrichedTensorProduct.of])
    (by simp only [mapThenTensor, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
      tensorEnrichedFunctors_data, EnrichedTensorProduct.of])
    (by simp only [mapThenTensor, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
      tensorEnrichedFunctors_data, EnrichedTensorProduct.of])
    (by simp only [tensorThenMap, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
      EnrichedTensorProduct.of])
    (by simp only [tensorThenMap, EnrichedFunctor.comp, canonicalTensor, MonoidalCategory.tensor_obj, reobject_data,
      EnrichedTensorProduct.of])
    (mapThenTensor_map_heq V F (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y'))
    (tensorThenMap_map_heq V F (EnrichedTensorProduct.of V X Y) (EnrichedTensorProduct.of V X' Y'))
    (tensoratorApp_heq V F m.coreMonoidal (EnrichedTensorProduct.of V X Y))
    (tensoratorApp_heq V F m.coreMonoidal (EnrichedTensorProduct.of V X' Y'))
  simpa only [Category.assoc, ForgetEnrichment.homOf_homTo, EnrichedTensorProduct.of,
    EnrichedFunctor.forget, ForgetEnrichment.of, ForgetEnrichment.to] using ht.mp hn
end
end RMod

namespace RMod
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]
  [M : MonoidalEnrichedCategory V C]

set_option backward.isDefEq.respectTransparency false in
theorem MonoidalEnrichedCategory.associator_naturality : ∀ X X' Y Y' Z Z' : ForgetEnrichment V C,
    (enrichedTensorMap V M.tensor M.tensor_objects X X' Y Y' ⊗ₘ 𝟙 (Z ⟶[V] Z')) ≫
      enrichedTensorMap V M.tensor M.tensor_objects (X ⊗ Y) (X' ⊗ Y') Z Z' ≫
      eHomWhiskerLeft V ((X ⊗ Y) ⊗ Z) (α_ X' Y' Z').hom =
    (α_ (X ⟶[V] X') (Y ⟶[V] Y') (Z ⟶[V] Z')).hom ≫
      (𝟙 (X ⟶[V] X') ⊗ₘ enrichedTensorMap V M.tensor M.tensor_objects Y Y' Z Z') ≫
      enrichedTensorMap V M.tensor M.tensor_objects X X' (Y ⊗ Z) (Y' ⊗ Z') ≫
      eHomWhiskerRight V (α_ X Y Z).hom (X' ⊗ (Y' ⊗ Z')) :=
  (associator_isGradedNatural_iff V M.tensor M.tensor_objects).1 M.associator_isGradedNatural

set_option backward.isDefEq.respectTransparency false in
theorem MonoidalEnrichedCategory.left_naturality : ∀ X Y : ForgetEnrichment V C,
    (λ_ (X ⟶[V] Y)).inv ≫
      (eId V (𝟙_ (ForgetEnrichment V C)) ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
      enrichedTensorMap V M.tensor M.tensor_objects (𝟙_ _) (𝟙_ _) X Y ≫
      eHomWhiskerLeft V ((𝟙_ _) ⊗ X) (λ_ Y).hom =
    eHomWhiskerRight V (λ_ X).hom Y :=
  (leftUnitor_isGradedNatural_iff V M.tensor M.tensor_objects).1 M.leftUnitor_isGradedNatural

set_option backward.isDefEq.respectTransparency false in
theorem MonoidalEnrichedCategory.right_naturality : ∀ X Y : ForgetEnrichment V C,
    (ρ_ (X ⟶[V] Y)).inv ≫
      (𝟙 (X ⟶[V] Y) ⊗ₘ eId V (𝟙_ (ForgetEnrichment V C))) ≫
      enrichedTensorMap V M.tensor M.tensor_objects X Y (𝟙_ _) (𝟙_ _) ≫
      eHomWhiskerLeft V (X ⊗ (𝟙_ _)) (ρ_ Y).hom =
    eHomWhiskerRight V (ρ_ X).hom Y :=
  (rightUnitor_isGradedNatural_iff V M.tensor M.tensor_objects).1 M.rightUnitor_isGradedNatural

end

end RMod

namespace RMod
/-! The canonical identification preserves composition and the specified grading. -/
private theorem categoryStruct_comp_transport {C : Type u} (A B : CategoryStruct.{0} C)
    (h : A = B) {X Y Z : C} (f : @Quiver.Hom C A.toQuiver X Y) (g : @Quiver.Hom C A.toQuiver Y Z) :
    cast (congrArg (fun d : CategoryStruct C => d.Hom X Z) h) (@CategoryStruct.comp C A X Y Z f g) =
      @CategoryStruct.comp C B X Y Z
        (cast (congrArg (fun d : CategoryStruct C => d.Hom X Y) h) f)
        (cast (congrArg (fun d : CategoryStruct C => d.Hom Y Z) h) g) := by
  cases h
  rfl

theorem totalHom_comp {C : Type u} [SuperCategory C] {X Y Z : TotalCategory C}
    (f : THom C X Y) (g : THom C Y Z) : totalHom (tComp C f g) = totalHom f ≫ totalHom g :=
  categoryStruct_comp_transport _ _ (totalCategoryCategory_data C).symm f g

private theorem submodule_mem_transport {A B : Type} (h : A = B)
    (gA : AddCommGroup A) (gB : AddCommGroup B)
    (mA : @Module ℝ A _ gA.toAddCommMonoid) (mB : @Module ℝ B _ gB.toAddCommMonoid)
    (hg : HEq gA gB) (hm : HEq mA mB)
    (P : @Submodule ℝ A _ gA.toAddCommMonoid mA) (Q : @Submodule ℝ B _ gB.toAddCommMonoid mB)
    (hp : HEq P Q) (x : A) (y : B) (hx : HEq x y) : x ∈ P ↔ y ∈ Q := by
  subst B
  cases eq_of_heq hg
  cases eq_of_heq hm
  cases hp
  cases hx
  rfl

theorem totalHom_mem_grade_iff {C : Type u} [SuperCategory C] {X Y : TotalCategory C}
    (f : THom C X Y) (a : ZMod 2) : totalHom f ∈ grade C X Y a ↔
      f ∈ (Submodule.pi {a}ᶜ (fun _ => ⊥) : Submodule ℝ (THom C X Y)) :=
  submodule_mem_transport
    (congrArg (fun d : CategoryStruct (TotalCategory C) => d.Hom X Y) (totalCategoryCategory_data C))
    _ _ _ _ (totalCategoryPreadditive_data C X Y) (totalCategoryLinear_data C X Y)
    _ _ (grade_data C X Y a) _ _ (cast_heq _ _)
end RMod

namespace RMod
/-! Derived transformations and ordinary equivalences reuse the prescribed components. -/
section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]

/-- Package the given components; no new component choice is made. -/
def gradedNatTransOfApp {A : Center V} {F G : EnrichedFunctor V C D}
    (app : ∀ X, A.1 ⟶ F.obj X ⟶[V] G.obj X)
    (h : IsGradedNaturalApp V A F G app) : GradedNatTrans A F G := ⟨app, h⟩

/-- Canonical degree-zero transformations, retaining exactly the ordinary components. -/
def EnrichedNatIso₀.hom {F G : EnrichedFunctor V C D} (e : EnrichedNatIso₀ V F G) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G :=
  gradedNatTransOfApp V _ e.hom_naturality

def EnrichedNatIso₀.inv {F G : EnrichedFunctor V C D} (e : EnrichedNatIso₀ V F G) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G F :=
  gradedNatTransOfApp V _ (e.inv_naturality V)

/-- Mathlib adjointifies the given ordinary isomorphisms without changing either functor. -/
def EnrichedEquivalence.forget (e : EnrichedEquivalence V C D) :
    ForgetEnrichment V C ≌ ForgetEnrichment V D :=
  CategoryTheory.Equivalence.mk e.functor.forget e.inverse.forget
    ((EnrichedFunctor.forgetId V C).symm ≪≫ e.unitIso.toNatIso ≪≫ e.functor.forgetComp e.inverse)
    ((e.inverse.forgetComp e.functor).symm ≪≫ e.counitIso.toNatIso ≪≫
      EnrichedFunctor.forgetId V D)
end

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u} [EnrichedCategory V C] [MonoidalCategory (ForgetEnrichment V C)]

variable [M : MonoidalEnrichedCategory V C]

/-- The canonical ordinary associator packaged as a degree-zero graded transformation. -/
def associatorGradedNatTrans :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (leftAssociatedTensor V M.tensor M.tensor_objects) (rightAssociatedTensor V M.tensor M.tensor_objects) :=
  gradedNatTransOfApp V (associatorApp V M.tensor M.tensor_objects) M.associator_isGradedNatural

/-- The canonical ordinary leftUnitor packaged as a degree-zero graded transformation. -/
def leftUnitorGradedNatTrans :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (leftUnitTensor V M.tensor M.tensor_objects) (EnrichedFunctor.id V C) :=
  gradedNatTransOfApp V (leftUnitorApp V M.tensor M.tensor_objects) M.leftUnitor_isGradedNatural

/-- The canonical ordinary rightUnitor packaged as a degree-zero graded transformation. -/
def rightUnitorGradedNatTrans :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (rightUnitTensor V M.tensor M.tensor_objects) (EnrichedFunctor.id V C) :=
  gradedNatTransOfApp V (rightUnitorApp V M.tensor M.tensor_objects) M.rightUnitor_isGradedNatural
end

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type u₁} {D : Type u₂} [EnrichedCategory V C] [EnrichedCategory V D]
  [MonoidalCategory (ForgetEnrichment V C)] [MonoidalCategory (ForgetEnrichment V D)]
  [MonoidalEnrichedCategory V C] [MonoidalEnrichedCategory V D]

def MonoidalEnrichedFunctor.tensoratorGradedNatTrans {F : EnrichedFunctor V C D}
    (m : MonoidalEnrichedFunctor V F) :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) (mapThenTensor V F) (tensorThenMap V F) :=
  gradedNatTransOfApp V _ m.tensorator_naturality
end

section
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  (C : Type u₁) (D : Type u₂) [EnrichedCategory V C] [EnrichedCategory V D]
  [MonoidalCategory (ForgetEnrichment V C)] [MonoidalCategory (ForgetEnrichment V D)]
  [MonoidalEnrichedCategory V C] [MonoidalEnrichedCategory V D]

/-- The ordinary equivalence uses the existing forward monoidal data. -/
@[implicit_reducible] def MonoidalEnrichedEquivalence.forgetMonoidal (e : MonoidalEnrichedEquivalence V C D) :
    (e.toEnrichedEquivalence.forget V).functor.Monoidal := e.monoidal.coreMonoidal.toMonoidal

/-- Mathlib canonically supplies the inverse ordinary monoidal structure. -/
@[implicit_reducible] def MonoidalEnrichedEquivalence.forgetInverseMonoidal (e : MonoidalEnrichedEquivalence V C D) :
    (e.toEnrichedEquivalence.forget V).inverse.Monoidal :=
  letI := e.forgetMonoidal V C D
  (e.toEnrichedEquivalence.forget V).inverseMonoidal
end
end RMod
