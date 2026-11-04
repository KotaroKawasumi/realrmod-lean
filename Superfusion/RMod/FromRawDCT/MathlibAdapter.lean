import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Superfusion.Category.Even
import Superfusion.Category.Monoidal
import Superfusion.Category.Supercategory
import Superfusion.RMod.FromRawDCT.Finite

/-!
# Mathlib proof-layer views of a raw-DCT coordinate envelope

This abstract file exposes the already proved finite-coordinate category as
Mathlib's category, preadditive, linear, and supercategory structures.  The
views add no executable data to a raw DCT or to `CandidateData`; they are
defined only so that general proof-layer results about exact pairings can be
reused later.

No concrete real table or instance is constructed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open CategoryTheory
open RawDCT

namespace MathlibAdapter

/-! ## Category and linear views -/

/-- The Mathlib category carried by the exact operations of `D`. -/
@[implicit_reducible]
def category (D : D) : Category Obj where
  Hom := Hom D.data
  id := Hom.id D.data
  comp := Hom.comp
  id_comp := Hom.id_comp D.laws
  comp_id := Hom.comp_id D.laws
  assoc := Hom.comp_assoc D.laws

/-- The pointwise preadditive view of the finite coordinate Hom matrices. -/
@[implicit_reducible]
def preadditive (D : D) :
    letI := category D
    Preadditive Obj := by
  letI := category D
  letI : Fact (DLaws D.data) := ⟨D.laws⟩
  exact
    { homGroup := fun X Y => by
        change AddCommGroup (Hom D.data X Y)
        infer_instance
      add_comp := by
        intro X Y Z f g h
        change Hom.comp (Hom.add f g) h =
          Hom.add (Hom.comp f h) (Hom.comp g h)
        exact Hom.add_comp D.laws f g h
      comp_add := by
        intro X Y Z f g h
        change Hom.comp f (Hom.add g h) =
          Hom.add (Hom.comp f g) (Hom.comp f h)
        exact Hom.comp_add D.laws f g h }

/-- The pointwise real-linear view of the finite coordinate Hom matrices. -/
@[implicit_reducible]
def linear (D : D) :
    letI := category D
    letI := preadditive D
    Linear ℝ Obj := by
  letI := category D
  letI := preadditive D
  letI : Fact (DLaws D.data) := ⟨D.laws⟩
  exact
    { homModule := fun X Y => by
        change Module ℝ (Hom D.data X Y)
        infer_instance
      smul_comp := by
        intro X Y Z r f g
        change Hom.comp (Hom.smul r f) g = Hom.smul r (Hom.comp f g)
        exact Hom.smul_comp D.laws r f g
      comp_smul := by
        intro X Y Z f r g
        change Hom.comp f (Hom.smul r g) = Hom.smul r (Hom.comp f g)
        exact Hom.comp_smul D.laws r f g }

/-! ## Hom grading -/

/-- The raw homogeneous carrier as a real submodule. -/
def grade (D : D) :
    letI := category D
    letI := preadditive D
    letI := linear D
    (X Y : Obj) → ZMod 2 → Submodule ℝ (X ⟶ Y) := by
  letI := category D
  letI := preadditive D
  letI := linear D
  intro X Y a
  exact
    { carrier := {f | Hom.MemGrade a f}
      zero_mem' := by
        change Hom.MemGrade a (Hom.zero D.data X Y)
        exact Hom.zero_memGrade D.laws a
      add_mem' := by
        intro f g hf hg
        change Hom.MemGrade a f at hf
        change Hom.MemGrade a g at hg
        change Hom.MemGrade a (Hom.add f g)
        exact Hom.add_memGrade D.laws f g hf hg
      smul_mem' := by
        intro r f hf
        change Hom.MemGrade a f at hf
        change Hom.MemGrade a (Hom.smul r f)
        exact Hom.smul_memGrade D.laws r f hf }

/-- The two raw parity pieces form an internal direct sum. -/
theorem grade_isInternal (D : D) :
    letI := category D
    letI := preadditive D
    letI := linear D
    ∀ X Y : Obj, DirectSum.IsInternal (grade D X Y) := by
  letI := category D
  letI := preadditive D
  letI := linear D
  intro X Y
  rw [DirectSum.isInternal_submodule_iff_isCompl (grade D X Y)
    (by decide : (0 : ZMod 2) ≠ 1)
    (by
      ext i
      rcases zmod2_cases i with hi | hi <;> subst i <;> simp)]
  constructor
  · rw [Submodule.disjoint_def]
    intro f hf₀ hf₁
    change Hom.MemGrade 0 f at hf₀
    change Hom.MemGrade 1 f at hf₁
    exact Hom.grade_disjoint D.laws 0 f hf₀ (by simpa using hf₁)
  · rw [codisjoint_iff]
    apply top_unique
    intro f _
    obtain ⟨f₀, f₁, hf₀, hf₁, hsum⟩ :=
      Hom.grade_decomposition D.laws f
    rw [← hsum]
    exact Submodule.add_mem_sup
      (show f₀ ∈ grade D X Y 0 from hf₀)
      (show f₁ ∈ grade D X Y 1 from hf₁)

/-- The Mathlib supercategory view of the exact raw grading. -/
@[implicit_reducible]
def supercategory (D : D) :
    letI := category D
    letI := preadditive D
    letI := linear D
    Superfusion.Category.Supercategory ℝ Obj := by
  letI := category D
  letI := preadditive D
  letI := linear D
  exact
    { grade := grade D
      isInternal_grade := grade_isInternal D
      id_mem_even := Hom.id_even D.laws
      comp_mem := fun f g hf hg => Hom.comp_memGrade D.laws f g hf hg }

/-! ## Finite biproducts in the even subcategory -/

/-- The canonical flattened coordinate tuple, viewed as a bicone of even
morphisms. -/
noncomputable def evenBicone (x : RawDCTData) (hD : DLaws x.D) :
    let D : D := ⟨x.D, hD⟩
    letI := category D
    letI := preadditive D
    letI := linear D
    letI := supercategory D
    {n : ℕ} →
      (S : Fin n → Superfusion.Category.EvenSubcategory ℝ Obj) →
        Limits.Bicone S := by
  dsimp only
  intro n S
  let D : D := ⟨x.D, hD⟩
  letI := category D
  letI := preadditive D
  letI := linear D
  letI := supercategory D
  let family : Fin n → Obj := fun i => (S i).obj
  exact
    { pt := Superfusion.Category.evenObj ℝ Obj (Finite.sumObj family)
      π := fun i =>
        ⟨Finite.familyProjection (dD := x.D) family i,
          Finite.familyProjection_even hD family i⟩
      ι := fun i =>
        ⟨Finite.familyInclusion (dD := x.D) family i,
          Finite.familyInclusion_even hD family i⟩
      ι_π := by
        classical
        intro i j
        by_cases hij : i = j
        · subst j
          apply WideSubcategory.hom_ext
          simp only
          change
            Hom.comp (Finite.familyInclusion (dD := x.D) family i)
                (Finite.familyProjection (dD := x.D) family i) =
              Hom.id x.D (family i)
          exact Finite.familyInclusion_projection_self hD family i
        · apply WideSubcategory.hom_ext
          simp only [dif_neg hij]
          change
            Hom.comp (Finite.familyInclusion (dD := x.D) family i)
                (Finite.familyProjection (dD := x.D) family j) =
              Hom.zero x.D (family i) (family j)
          exact Finite.familyInclusion_projection_ne hD family i j hij }

/-- The canonical even bicone satisfies the total-resolution identity. -/
theorem evenBicone_total (x : RawDCTData) (hD : DLaws x.D)
    (rows : UnitRowsData x.D x.C) :
    let D : D := ⟨x.D, hD⟩
    letI := category D
    letI := preadditive D
    letI := linear D
    letI := supercategory D
    ∀ {n : ℕ}
      (S : Fin n → Superfusion.Category.EvenSubcategory ℝ Obj),
        ∑ i, (evenBicone x hD S).π i ≫
            (evenBicone x hD S).ι i =
          𝟙 (evenBicone x hD S).pt := by
  dsimp only
  intro n S
  let D : D := ⟨x.D, hD⟩
  letI := category D
  letI := preadditive D
  letI := linear D
  letI := supercategory D
  letI : Fact (DLaws x.D) := ⟨hD⟩
  apply WideSubcategory.hom_ext
  let family : Fin n → Obj := fun i => (S i).obj
  have htotal := Finite.familyProjection_inclusion_total
    x rows family
  rw [Finite.candidateFinSum_eq_sum x rows] at htotal
  let P := Superfusion.Category.evenMorphismProperty ℝ Obj
  let F := wideSubcategoryInclusion P
  change F.map (∑ i, (evenBicone x hD S).π i ≫
      (evenBicone x hD S).ι i) =
    F.map (𝟙 (evenBicone x hD S).pt)
  rw [Functor.map_sum]
  rw [F.map_id]
  simp_rw [F.map_comp]
  change
    (∑ i, Hom.comp (Finite.familyProjection (dD := x.D) family i)
        (Finite.familyInclusion (dD := x.D) family i)) =
      Hom.id x.D (Finite.sumObj family)
  exact htotal

/-- The even subcategory of every finite raw coordinate envelope has finite
biproducts, chosen by canonical flattening. -/
@[implicit_reducible]
noncomputable def evenHasFiniteBiproducts (x : RawDCTData)
    (hD : DLaws x.D) (rows : UnitRowsData x.D x.C) :
    let D : D := ⟨x.D, hD⟩
    letI := category D
    letI := preadditive D
    letI := linear D
    letI := supercategory D
    Limits.HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) := by
  let D : D := ⟨x.D, hD⟩
  letI := category D
  letI := preadditive D
  letI := linear D
  letI := supercategory D
  refine ⟨fun n => ⟨fun S => ?_⟩⟩
  exact Limits.hasBiproduct_of_total
    (evenBicone x hD S) (evenBicone_total x hD rows S)

/-! ## Monoidal-super view -/

/-- The Mathlib monoidal formation data carried by the exact raw tensor,
associator, and unitors.  Only `MonoidalCategoryStruct` is used because the
interchange law is the signed super-interchange law. -/
@[implicit_reducible]
def monoidalCategoryStruct (D : D) (tensor : Tensor D)
    (associator : Associator D tensor)
    (unitor : Unitor D tensor associator) :
    letI := category D
    MonoidalCategoryStruct Obj := by
  letI := category D
  exact
    { tensorObj := tensor.data.tensorObj
      whiskerLeft := fun X {_ _} f =>
        tensor.data.tensorHom (Hom.id D.data X) f
      whiskerRight := fun {_ _} f Y =>
        tensor.data.tensorHom f (Hom.id D.data Y)
      tensorHom := tensor.data.tensorHom
      tensorUnit := unitor.data.tensorUnit
      associator := fun X Y Z =>
        { hom := associator.data.associatorHom X Y Z
          inv := associator.data.associatorInv X Y Z
          hom_inv_id := associator.laws.associator_hom_inv X Y Z
          inv_hom_id := associator.laws.associator_inv_hom X Y Z }
      leftUnitor := fun X =>
        { hom := unitor.data.leftUnitorHom X
          inv := unitor.data.leftUnitorInv X
          hom_inv_id := unitor.laws.leftUnitor_hom_inv X
          inv_hom_id := unitor.laws.leftUnitor_inv_hom X }
      rightUnitor := fun X =>
        { hom := unitor.data.rightUnitorHom X
          inv := unitor.data.rightUnitorInv X
          hom_inv_id := unitor.laws.rightUnitor_hom_inv X
          inv_hom_id := unitor.laws.rightUnitor_inv_hom X } }

/-- The existing raw laws, viewed as Mathlib's monoidal-super laws for the
same exact formation data. -/
@[implicit_reducible]
def monoidalSupercategory (D : D) (tensor : Tensor D)
    (associator : Associator D tensor)
    (unitor : Unitor D tensor associator) :
    letI := category D
    letI := preadditive D
    letI := linear D
    letI := supercategory D
    letI := monoidalCategoryStruct D tensor associator unitor
    Superfusion.Category.MonoidalSupercategory ℝ Obj := by
  letI := category D
  letI := preadditive D
  letI := linear D
  letI := supercategory D
  letI := monoidalCategoryStruct D tensor associator unitor
  exact
    { tensorHom_mem := fun f g hf hg =>
        tensor.laws.tensor_grade f g hf hg
      tensor_id := tensor.laws.tensor_id
      tensor_add_left := tensor.laws.tensor_add_left
      tensor_add_right := tensor.laws.tensor_add_right
      tensor_smul_left := tensor.laws.tensor_smul_left
      tensor_smul_right := tensor.laws.tensor_smul_right
      super_interchange := tensor.laws.super_interchange
      whiskerLeft_eq := fun X {_ _} g => rfl
      whiskerRight_eq := fun {_ _} f Z => rfl
      associator_hom_mem := associator.laws.associator_hom_even
      associator_inv_mem := associator.laws.associator_inv_even
      associator_naturality := associator.laws.associator_naturality
      leftUnitor_hom_mem := unitor.laws.leftUnitor_hom_even
      leftUnitor_inv_mem := unitor.laws.leftUnitor_inv_even
      leftUnitor_naturality := unitor.laws.leftUnitor_naturality
      rightUnitor_hom_mem := unitor.laws.rightUnitor_hom_even
      rightUnitor_inv_mem := unitor.laws.rightUnitor_inv_even
      rightUnitor_naturality := unitor.laws.rightUnitor_naturality
      pentagon := by
        intro W X Y Z
        rw [← Category.assoc]
        exact associator.laws.pentagon W X Y Z
      triangle := by
        intro X Y
        change
          Hom.comp
              (associator.data.associatorHom X
                unitor.data.tensorUnit Y)
              (tensor.data.tensorHom (Hom.id D.data X)
                (unitor.data.leftUnitorHom Y)) =
            tensor.data.tensorHom (unitor.data.rightUnitorHom X)
              (Hom.id D.data Y)
        exact unitor.laws.triangle X Y }

end MathlibAdapter

end Superfusion.RMod.FromRawDCT
