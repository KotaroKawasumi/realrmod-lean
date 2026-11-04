import RMod.Enriched.Compatibility

/-! The Hom-object naturality conditions imply the total-morphism equations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators TensorProduct
universe u u₁ u₂ v w
/-! All equations below use the independent, fully implemented enrichment. -/

namespace RMod.Regression
/-! Total-morphism notation is needed only for these compatibility checks. -/
abbrev EHom (C : Type u) [SuperCategory C] (X Y : C) := 𝟙_ SuperVec ⟶ SHom C X Y

/-! The total action is obtained componentwise from an enriched functor. -/
def tMap {C : Type u₁} {D : Type u₂} [SuperCategory C] [SuperCategory D] (F : SuperFunctor C D)
    {X Y : C} (f : THom C X Y) : THom D (F.obj X) (F.obj Y) :=
  fun a => F.map X Y a (f a)

/-! Specializing the hom-object tensor to SuperVec sums over both homogeneous degrees.
The product enrichment above uses superVecSymmetric, hence the prescribed Koszul sign. -/
def tTensor {C : Type u} [SuperCategory C] [MonoidalCategory (Even C)]
    [M : MonoidalEnrichedCategory SuperVec C]
    {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y') :
    THom C (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y') := fun a =>
  enrichedTensorMap SuperVec M.tensor M.tensor_objects X X' Y Y' a
    (∑ i : ZMod 2, GradedObject.Monoidal.ιTensorObj (SHom C X X') (SHom C Y Y')
      i (a - i) a ((add_comm i (a - i)).trans (sub_add_cancel a i)) (f i ⊗ₜ[ℝ] g (a - i)))

open GradedObject.Monoidal
set_option backward.isDefEq.respectTransparency false
section TotalComposition
variable (C : Type u) [SuperCategory C]

theorem comp_even_left {X Y Z : C} (f : EHom C X Y) (g : THom C Y Z) (a : ZMod 2) :
    tComp C (evenPoint f) g a = eComp SuperVec X Y Z a
      (ιTensorObj (SHom C X Y) (SHom C Y Z) 0 a a (zero_add a)
        (evenPoint f 0 ⊗ₜ[ℝ] g a)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single 0]
  · fin_cases a <;> rfl
  · intro b _ hb
    simp [evenPoint, homogeneousPoint, hb]
  · simp

theorem comp_even_right {X Y Z : C} (f : THom C X Y) (g : EHom C Y Z) (a : ZMod 2) :
    tComp C f (evenPoint g) a = eComp SuperVec X Y Z a
      (ιTensorObj (SHom C X Y) (SHom C Y Z) a 0 a (add_zero a)
        (f a ⊗ₜ[ℝ] evenPoint g 0)) := by
  classical
  unfold tComp
  rw [Finset.sum_eq_single a]
  · fin_cases a <;> rfl
  · intro b _ hb
    have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    simp [evenPoint, homogeneousPoint, hab]
  · simp

theorem pre_apply {X Y Z : Even C} (f : X ⟶ Y) (g : THom C Y Z) (a : ZMod 2) :
    eHomWhiskerRight SuperVec f Z a (g a) =
      tComp C (evenPoint (ForgetEnrichment.homTo SuperVec f)) g a := by
  rw [comp_even_left]
  change ((GradedObject.Monoidal.leftUnitor (SHom C Y Z)).inv a ≫
    GradedObject.Monoidal.tensorHom (ForgetEnrichment.homTo SuperVec f) (𝟙 (SHom C Y Z)) a ≫
    eComp SuperVec (X : C) Y Z a) (g a) = _
  erw [GradedObject.Monoidal.leftUnitor_inv_apply, Category.assoc, Category.assoc,
    ι_tensorHom_assoc]
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀]
  rfl

theorem post_apply {X Y Z : Even C} (f : THom C X Y) (g : Y ⟶ Z) (a : ZMod 2) :
    eHomWhiskerLeft SuperVec X g a (f a) =
      tComp C f (evenPoint (ForgetEnrichment.homTo SuperVec g)) a := by
  rw [comp_even_right]
  change ((GradedObject.Monoidal.rightUnitor (SHom C X Y)).inv a ≫
    GradedObject.Monoidal.tensorHom (𝟙 (SHom C X Y)) (ForgetEnrichment.homTo SuperVec g) a ≫
    eComp SuperVec (X : C) Y Z a) (f a) = _
  erw [GradedObject.Monoidal.rightUnitor_inv_apply, Category.assoc, Category.assoc,
    ι_tensorHom_assoc]
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀]
  rfl
end TotalComposition

section Naturality
variable {C : Type u₁} {D : Type u₂} [SuperCategory C] [SuperCategory D]

theorem graded_naturality_total {F G : SuperFunctor C D}
    (α : GradedNatTrans ((Center.ofBraided SuperVec).obj (𝟙_ SuperVec)) F G)
    {X Y : C} (f : THom C X Y) :
    tComp D (tMap F f) (evenPoint (α.app Y)) =
      tComp D (evenPoint (α.app X)) (tMap G f) := by
  have h := (degreeZero_naturality_iff SuperVec F G α.app).1 α.naturality X Y
  have h' := congrArg (fun k => fun a : ZMod 2 => k a (f a)) h
  funext a
  have ha := congrFun h' a
  change eHomWhiskerLeft SuperVec (ForgetEnrichment.of SuperVec (F.obj X))
      (ForgetEnrichment.homOf SuperVec (α.app Y)) a (tMap F f a) =
    eHomWhiskerRight SuperVec (ForgetEnrichment.homOf SuperVec (α.app X))
      (ForgetEnrichment.of SuperVec (G.obj Y)) a (tMap G f a) at ha
  simpa only [post_apply, pre_apply, ForgetEnrichment.homTo_homOf] using ha
/-- Evaluate a Hom-object naturality equation on arbitrary total vectors. -/
theorem hom_equation_total {H : SuperVec} {A B A' B' : Even D}
    (f : H ⟶ SHom D A B) (g : H ⟶ SHom D A' B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ eHomWhiskerLeft SuperVec A b = g ≫ eHomWhiskerRight SuperVec a B')
    (p : ∀ r, H r) :
    tComp D (fun r => f r (p r)) (evenPoint (ForgetEnrichment.homTo SuperVec b)) =
      tComp D (evenPoint (ForgetEnrichment.homTo SuperVec a)) (fun r => g r (p r)) := by
  funext r
  have hr := congrArg (fun k => k r (p r)) h
  change eHomWhiskerLeft SuperVec A b r (f r (p r)) =
    eHomWhiskerRight SuperVec a B' r (g r (p r)) at hr
  rw [← post_apply D (fun r => f r (p r)) b r,
    ← pre_apply D a (fun r => g r (p r)) r]
  exact hr
end Naturality
end RMod.Regression


namespace RMod.Regression
open GradedObject.Monoidal
set_option backward.isDefEq.respectTransparency false

/-- The same convolution point used by tTensor, before applying the enriched tensor map. -/
def tensorPoint {A B : SuperVec} (x : ∀ a, A a) (y : ∀ a, B a) : ∀ a, (A ⊗ B) a :=
  fun a => ∑ i : ZMod 2, ιTensorObj A B i (a - i) a
    ((add_comm i (a - i)).trans (sub_add_cancel a i)) (x i ⊗ₜ[ℝ] y (a - i))

/-- Naturality of convolution in both graded linear maps. -/
theorem tensorPoint_map {A B A' B' : SuperVec} (f : A ⟶ A') (g : B ⟶ B')
    (x : ∀ a, A a) (y : ∀ a, B a) :
    (fun a => (f ⊗ₘ g) a (tensorPoint x y a)) =
      tensorPoint (fun a => f a (x a)) (fun a => g a (y a)) := by
  funext a
  change (GradedObject.Monoidal.tensorHom f g a) (∑ i : ZMod 2, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (ιTensorObj A B i (a - i) a _ ≫ GradedObject.Monoidal.tensorHom f g a)
    (x i ⊗ₜ[ℝ] y (a - i)) = _
  rw [ι_tensorHom]
  rfl

section Monoidal
variable {C : Type u₁} {D : Type u₂} [SuperCategory C] [SuperCategory D]
  [MonoidalCategory (Even C)] [MonoidalCategory (Even D)]
  [MC : MonoidalEnrichedCategory SuperVec C] [MD : MonoidalEnrichedCategory SuperVec D]

theorem tensor_natural {F : SuperFunctor C D} (m : MonoidalEnrichedFunctor SuperVec F)
    {X X' Y Y' : Even C} (f : THom C X X') (g : THom C Y Y') :
    tComp D (tTensor (C := D) (tMap F f) (tMap F g))
      (evenPoint (m.coreMonoidal.μIso X' Y').hom) =
    tComp D (evenPoint (m.coreMonoidal.μIso X Y).hom) (tMap F (tTensor (C := C) f g)) := by
  let L := (F.map X X' ⊗ₘ F.map Y Y') ≫
    enrichedTensorMap SuperVec MD.tensor MD.tensor_objects (F.obj X) (F.obj X') (F.obj Y) (F.obj Y')
  let R := enrichedTensorMap SuperVec MC.tensor MC.tensor_objects X X' Y Y' ≫
    F.map (tensorObj (C := Even C) X Y) (tensorObj (C := Even C) X' Y')
  have hn := hom_equation_total L R (m.coreMonoidal.μIso X Y).hom (m.coreMonoidal.μIso X' Y').hom
    (by simpa only [L, R, Category.assoc, EnrichedFunctor.forget, ForgetEnrichment.of,
      ForgetEnrichment.to] using m.tensor_naturality SuperVec X X' Y Y') (tensorPoint f g)
  have hl : (fun a => L a (tensorPoint f g a)) = tTensor (C := D) (tMap F f) (tMap F g) := by
    funext a
    change enrichedTensorMap SuperVec MD.tensor MD.tensor_objects _ _ _ _ a
      ((F.map X X' ⊗ₘ F.map Y Y') a (tensorPoint f g a)) = _
    rw [congrFun (tensorPoint_map (F.map X X') (F.map Y Y') f g) a]
    rfl
  rw [hl] at hn
  exact hn


variable (e : MonoidalEnrichedEquivalence SuperVec C D)

theorem unit_natural {X Y : C} (f : THom C X Y) :
    tComp C f (evenPoint (e.unitIso.toNatIso.hom.app (ForgetEnrichment.of SuperVec Y))) =
    tComp C (evenPoint (e.unitIso.toNatIso.hom.app (ForgetEnrichment.of SuperVec X)))
      (tMap e.inverse (tMap e.functor f)) := by
  exact graded_naturality_total (e.unitIso.hom SuperVec) f

theorem counit_natural {X Y : D} (f : THom D X Y) :
    tComp D (tMap e.functor (tMap e.inverse f))
      (evenPoint (e.counitIso.toNatIso.hom.app (ForgetEnrichment.of SuperVec Y))) =
    tComp D (evenPoint (e.counitIso.toNatIso.hom.app (ForgetEnrichment.of SuperVec X))) f := by
  exact graded_naturality_total (e.counitIso.hom SuperVec) f

end Monoidal
end RMod.Regression


namespace RMod.Regression
open GradedObject.Monoidal
set_option backward.isDefEq.respectTransparency false

/-- Graded associativity acts on every pure homogeneous tensor without an extra sign. -/
theorem assoc_term (A B C : SuperVec) (i j k a : ZMod 2) (h : i + j + k = a)
    (x : A i) (y : B j) (z : C k) :
    (α_ A B C).hom a
      (ιTensorObj (GradedObject.Monoidal.tensorObj A B) C (i + j) k a h
        (ιTensorObj A B i j (i + j) rfl (x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z)) =
    ιTensorObj A (GradedObject.Monoidal.tensorObj B C) i (j + k) a ((add_assoc i j k).symm.trans h)
      (x ⊗ₜ[ℝ] ιTensorObj B C j k (j + k) rfl (y ⊗ₜ[ℝ] z)) := by
  change (ιTensorObj₃' A B C i j k a h ≫
    (GradedObject.Monoidal.associator A B C).hom a) ((x ⊗ₜ[ℝ] y) ⊗ₜ[ℝ] z) = _
  rw [ιTensorObj₃'_associator_hom]
  rfl

/-- Expanding the two degrees is used only to verify the convolution associator. -/
theorem sum_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ i, f i = f 0 + f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [h]
  simp

/-- Reassociation preserves the explicit convolution tensor points. -/
theorem tensorPoint_assoc {A B C : SuperVec}
    (x : ∀ a, A a) (y : ∀ a, B a) (z : ∀ a, C a) :
    (fun a => (α_ A B C).hom a (tensorPoint (tensorPoint x y) z a)) =
      tensorPoint x (tensorPoint y z) := by
  funext a
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  rcases ha with rfl | rfl <;>
    simp only [tensorPoint, sum_two, TensorProduct.add_tmul, TensorProduct.tmul_add, map_add]
  · erw [assoc_term A B C 0 0 0 0 rfl, assoc_term A B C 1 1 0 0 rfl,
      assoc_term A B C 0 1 1 0 rfl, assoc_term A B C 1 0 1 0 rfl]
    apply (show ∀ a b c d : ((A ⊗ B ⊗ C) _), a + b + (c + d) = a + c + (d + b) from by
      intros; abel)
  · erw [assoc_term A B C 0 0 1 1 rfl, assoc_term A B C 1 1 1 1 rfl,
      assoc_term A B C 0 1 0 1 rfl, assoc_term A B C 1 0 0 1 rfl]
    apply (show ∀ a b c d : ((A ⊗ B ⊗ C) _), a + b + (c + d) = a + c + (d + b) from by
      intros; abel)
end RMod.Regression


namespace RMod.Regression
open GradedObject.Monoidal
set_option backward.isDefEq.respectTransparency false

/-- Insertion of a degree-zero point agrees with the convolution tensor. -/
theorem tensorPoint_even_left {A B : SuperVec} (f : 𝟙_ SuperVec ⟶ A) (g : ∀ a, B a) :
    (fun a => ((λ_ B).inv ≫ (f ⊗ₘ 𝟙 B)) a (g a)) = tensorPoint (evenPoint f) g := by
  funext a
  change ((GradedObject.Monoidal.leftUnitor B).inv a ≫
    GradedObject.Monoidal.tensorHom f (𝟙 B) a) (g a) = _
  erw [GradedObject.Monoidal.leftUnitor_inv_apply, Category.assoc, Category.assoc, ι_tensorHom]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀]
  symm
  unfold tensorPoint
  rw [Finset.sum_eq_single 0]
  · fin_cases a <;> rfl
  · intro b _ hb
    simp [evenPoint, homogeneousPoint, hb]
  · simp

theorem tensorPoint_even_right {A B : SuperVec} (f : ∀ a, A a) (g : 𝟙_ SuperVec ⟶ B) :
    (fun a => ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ g)) a (f a)) = tensorPoint f (evenPoint g) := by
  funext a
  change ((GradedObject.Monoidal.rightUnitor A).inv a ≫
    GradedObject.Monoidal.tensorHom (𝟙 A) g a) (f a) = _
  erw [GradedObject.Monoidal.rightUnitor_inv_apply, Category.assoc, Category.assoc, ι_tensorHom]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    tensorUnit₀]
  symm
  unfold tensorPoint
  rw [Finset.sum_eq_single a]
  · fin_cases a <;> rfl
  · intro b _ hb
    have hab : a - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    simp [evenPoint, homogeneousPoint, hab]
  · simp

section Coherence
variable {C : Type u} [SuperCategory C] [MonoidalCategory (Even C)]
  [M : MonoidalEnrichedCategory SuperVec C]

/-- The new property implies the old associator law for arbitrary total morphisms. -/
theorem associator_natural {X X' Y Y' Z Z' : Even C}
    (f : THom C X X') (g : THom C Y Y') (h : THom C Z Z') :
    tComp C (tTensor (C := C) (tTensor (C := C) f g) h) (evenPoint (α_ X' Y' Z').hom) =
      tComp C (evenPoint (α_ X Y Z).hom) (tTensor (C := C) f (tTensor (C := C) g h)) := by
  let L := (enrichedTensorMap SuperVec M.tensor M.tensor_objects X X' Y Y' ⊗ₘ 𝟙 (SHom C Z Z')) ≫
    enrichedTensorMap SuperVec M.tensor M.tensor_objects (X ⊗ Y) (X' ⊗ Y') Z Z'
  let R := (α_ (SHom C X X') (SHom C Y Y') (SHom C Z Z')).hom ≫
    (𝟙 (SHom C X X') ⊗ₘ enrichedTensorMap SuperVec M.tensor M.tensor_objects Y Y' Z Z') ≫
      enrichedTensorMap SuperVec M.tensor M.tensor_objects X X' (Y ⊗ Z) (Y' ⊗ Z')
  have hn := hom_equation_total L R (α_ X Y Z).hom (α_ X' Y' Z').hom
    (by simpa only [L, R, Category.assoc] using
      MonoidalEnrichedCategory.associator_naturality SuperVec (C := C) X X' Y Y' Z Z')
    (tensorPoint (tensorPoint f g) h)
  have hl : (fun a => L a (tensorPoint (tensorPoint f g) h a)) =
      tTensor (C := C) (tTensor (C := C) f g) h := by
    funext a
    change enrichedTensorMap SuperVec M.tensor M.tensor_objects _ _ _ _ a
      ((enrichedTensorMap SuperVec M.tensor M.tensor_objects X X' Y Y' ⊗ₘ 𝟙 (SHom C Z Z')) a
        (tensorPoint (tensorPoint f g) h a)) = _
    erw [congrFun (tensorPoint_map _ _ (tensorPoint f g) h) a]
    rfl
  have hr : (fun a => R a (tensorPoint (tensorPoint f g) h a)) =
      tTensor (C := C) f (tTensor (C := C) g h) := by
    funext a
    change enrichedTensorMap SuperVec M.tensor M.tensor_objects _ _ _ _ a
      ((𝟙 (SHom C X X') ⊗ₘ enrichedTensorMap SuperVec M.tensor M.tensor_objects Y Y' Z Z') a
        ((α_ (SHom C X X') (SHom C Y Y') (SHom C Z Z')).hom a
          (tensorPoint (tensorPoint f g) h a))) = _
    erw [congrFun (tensorPoint_assoc f g h) a,
      congrFun (tensorPoint_map _ _ f (tensorPoint g h)) a]
    rfl
  rw [hl, hr] at hn
  exact hn

/-- Left unit naturality holds on odd as well as even morphisms. -/
theorem leftUnitor_natural {X Y : Even C} (f : THom C X Y) :
    tComp C (tTensor (C := C) (evenPoint (eId SuperVec (𝟙_ (Even C)))) f) (evenPoint (λ_ Y).hom) =
      tComp C (evenPoint (λ_ X).hom) f := by
  let L := (λ_ (SHom C X Y)).inv ≫ (eId SuperVec (𝟙_ (Even C)) ⊗ₘ 𝟙 (SHom C X Y)) ≫
    enrichedTensorMap SuperVec M.tensor M.tensor_objects (𝟙_ (Even C)) (𝟙_ (Even C)) X Y
  have hn := hom_equation_total L (𝟙 (SHom C X Y)) (λ_ X).hom (λ_ Y).hom
    (by simpa only [L, Category.assoc, Category.id_comp] using
      MonoidalEnrichedCategory.left_naturality SuperVec (C := C) X Y) f
  have hl : (fun a => L a (f a)) = tTensor (C := C) (evenPoint (eId SuperVec (𝟙_ (Even C)))) f := by
    funext a
    change enrichedTensorMap SuperVec M.tensor M.tensor_objects _ _ _ _ a
      (((λ_ (SHom C X Y)).inv ≫ (eId SuperVec (𝟙_ (Even C)) ⊗ₘ 𝟙 (SHom C X Y))) a (f a)) = _
    erw [congrFun (tensorPoint_even_left _ f) a]
    rfl
  rw [hl] at hn
  exact hn

/-- Right unit naturality holds on odd as well as even morphisms. -/
theorem rightUnitor_natural {X Y : Even C} (f : THom C X Y) :
    tComp C (tTensor (C := C) f (evenPoint (eId SuperVec (𝟙_ (Even C))))) (evenPoint (ρ_ Y).hom) =
      tComp C (evenPoint (ρ_ X).hom) f := by
  let L := (ρ_ (SHom C X Y)).inv ≫ (𝟙 (SHom C X Y) ⊗ₘ eId SuperVec (𝟙_ (Even C))) ≫
    enrichedTensorMap SuperVec M.tensor M.tensor_objects X Y (𝟙_ (Even C)) (𝟙_ (Even C))
  have hn := hom_equation_total L (𝟙 (SHom C X Y)) (ρ_ X).hom (ρ_ Y).hom
    (by simpa only [L, Category.assoc, Category.id_comp] using
      MonoidalEnrichedCategory.right_naturality SuperVec (C := C) X Y) f
  have hl : (fun a => L a (f a)) = tTensor (C := C) f (evenPoint (eId SuperVec (𝟙_ (Even C)))) := by
    funext a
    change enrichedTensorMap SuperVec M.tensor M.tensor_objects _ _ _ _ a
      (((ρ_ (SHom C X Y)).inv ≫ (𝟙 (SHom C X Y) ⊗ₘ eId SuperVec (𝟙_ (Even C)))) a (f a)) = _
    erw [congrFun (tensorPoint_even_right f _) a]
    rfl
  rw [hl] at hn
  exact hn

end Coherence
end RMod.Regression
