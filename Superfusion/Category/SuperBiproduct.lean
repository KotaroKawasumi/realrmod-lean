import Mathlib.CategoryTheory.Preadditive.Biproducts
import Superfusion.Category.Even

/-!
# Finite biproducts with visibly even structure maps

Suppose the even subcategory of a linear supercategory has finite
biproducts.  We forget its chosen biproduct object back to the total
supercategory.  The resulting projections and inclusions retain proofs
that they are even.

For an arbitrary componentwise family of total morphisms `p j`, the
diagonal extension

`∑ j, π j ≫ p j ≫ ι j`

is therefore homogeneous whenever all `p j` have one common degree.
This is the appropriate finite-sum API for convolution in a
supercategory: using an unrelated chosen biproduct in the total category
would not expose the degrees of its structure maps.
-/

set_option autoImplicit false

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace Superfusion.Category

noncomputable section

variable {K : Type u} [Field K]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear K C]
  [Supercategory K C]
  [HasFiniteBiproducts (EvenSubcategory K C)]
variable {J : Type x} [Finite J]

/-- A file-local enumeration of the finite indexing type.  Public
declarations retain only the invariant `[Finite J]` assumption. -/
noncomputable local instance finiteIndexFintype : Fintype J :=
  Fintype.ofFinite J

/-- The chosen finite biproduct in the even subcategory, regarded as an
object of the total supercategory. -/
noncomputable abbrev superBiproduct (S : J → C) : C :=
  (⨁ fun j => evenObj K C (S j)).obj

/-- The visibly even projection from a super-biproduct. -/
noncomputable def superBiproductπ (S : J → C) (j : J) :
    superBiproduct (K := K) S ⟶ S j :=
  (biproduct.π (fun j => evenObj K C (S j)) j).hom

/-- The visibly even inclusion into a super-biproduct. -/
noncomputable def superBiproductι (S : J → C) (j : J) :
    S j ⟶ superBiproduct (K := K) S :=
  (biproduct.ι (fun j => evenObj K C (S j)) j).hom

/-- Every chosen super-biproduct projection is even. -/
theorem superBiproductπ_mem (S : J → C) (j : J) :
    superBiproductπ (K := K) S j ∈
      homGrade K (superBiproduct (K := K) S) (S j) 0 :=
  (biproduct.π (fun j => evenObj K C (S j)) j).property

/-- Every chosen super-biproduct inclusion is even. -/
theorem superBiproductι_mem (S : J → C) (j : J) :
    superBiproductι (K := K) S j ∈
      homGrade K (S j) (superBiproduct (K := K) S) 0 :=
  (biproduct.ι (fun j => evenObj K C (S j)) j).property

/-- Inclusion followed by the matching projection is the identity. -/
@[simp]
theorem superBiproductι_π_self (S : J → C) (j : J) :
    superBiproductι (K := K) S j ≫
        superBiproductπ (K := K) S j =
      𝟙 (S j) := by
  have h := biproduct.ι_π_self
    (fun j => evenObj K C (S j)) j
  exact congrArg (fun q => q.hom) h

/-- Inclusion followed by a different projection is zero. -/
theorem superBiproductι_π_ne
    (S : J → C) {j k : J} (hjk : j ≠ k) :
    superBiproductι (K := K) S j ≫
        superBiproductπ (K := K) S k =
      0 := by
  have h := biproduct.ι_π_ne
    (fun j => evenObj K C (S j)) hjk
  exact congrArg (fun q => q.hom) h

/-- The finite sum of projection-inclusion pairs is the identity. -/
theorem superBiproduct_total (S : J → C) :
    ∑ j : J, superBiproductπ (K := K) S j ≫
        superBiproductι (K := K) S j =
      𝟙 (superBiproduct (K := K) S) := by
  classical
  have h := CategoryTheory.Limits.IsBilimit.total
    (biproduct.isBilimit (fun j : J => evenObj K C (S j)))
  let I := wideSubcategoryInclusion (evenMorphismProperty K C)
  have hm := congrArg (fun q => I.map q) h
  rw [I.map_sum
    (fun j : J =>
      biproduct.π (fun j => evenObj K C (S j)) j ≫
        biproduct.ι (fun j => evenObj K C (S j)) j)
    Finset.univ] at hm
  change
    (∑ j : J, superBiproductπ (K := K) S j ≫
      superBiproductι (K := K) S j) =
        𝟙 (superBiproduct (K := K) S) at hm
  exact hm

/-- A finite super-biproduct of zero objects is a zero object.

This is the visibly-even biproduct analogue of the elementary fact that
a finite direct sum of zero objects is zero.  It is useful when a
convolution has no active summands in a given output sector. -/
theorem superBiproduct_isZero
    (S : J → C) (hS : ∀ j, IsZero (S j)) :
    IsZero (superBiproduct (K := K) S) := by
  rw [IsZero.iff_id_eq_zero, ← superBiproduct_total (K := K) S]
  classical
  apply Finset.sum_eq_zero
  intro j _
  rw [(hS j).eq_of_tgt (superBiproductπ (K := K) S j), zero_comp]

/-- Diagonally extend a componentwise family of total morphisms between
finite super-biproducts. -/
noncomputable def superBiproductMap
    (S T : J → C) (p : ∀ j, S j ⟶ T j) :
    superBiproduct (K := K) S ⟶ superBiproduct (K := K) T := by
  classical
  exact ∑ j, superBiproductπ (K := K) S j ≫ p j ≫
    superBiproductι (K := K) T j

/-- Maps out of a super-biproduct are determined by their composites with
the visibly even inclusions. -/
theorem superBiproduct_hom_ext
    (S : J → C) {Z : C}
    (f g : superBiproduct (K := K) S ⟶ Z)
    (h : ∀ j, superBiproductι (K := K) S j ≫ f =
      superBiproductι (K := K) S j ≫ g) :
    f = g := by
  classical
  rw [← Category.id_comp f, ← Category.id_comp g,
    ← superBiproduct_total (K := K) S, sum_comp, sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Category.assoc, Category.assoc, h j]

/-- A diagonal map restricts to its selected component on each
inclusion. -/
@[reassoc (attr := simp)]
theorem superBiproductι_map
    (S T : J → C) (p : ∀ j, S j ⟶ T j) (j : J) :
    superBiproductι (K := K) S j ≫
        superBiproductMap (K := K) S T p =
      p j ≫ superBiproductι (K := K) T j := by
  classical
  rw [superBiproductMap, comp_sum]
  calc
    _ = superBiproductι (K := K) S j ≫
        superBiproductπ (K := K) S j ≫ p j ≫
          superBiproductι (K := K) T j := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [← Category.assoc, ← Category.assoc,
          superBiproductι_π_ne S hkj.symm, zero_comp, zero_comp]
      · simp
    _ = _ := by
      rw [← Category.assoc, ← Category.assoc,
        superBiproductι_π_self, Category.id_comp]

/-- A diagonal map followed by a selected projection is the selected
component preceded by the corresponding source projection. -/
@[reassoc (attr := simp)]
theorem superBiproductMap_π
    (S T : J → C) (p : ∀ j, S j ⟶ T j) (j : J) :
    superBiproductMap (K := K) S T p ≫
        superBiproductπ (K := K) T j =
      superBiproductπ (K := K) S j ≫ p j := by
  classical
  rw [superBiproductMap, sum_comp]
  calc
    _ = (superBiproductπ (K := K) S j ≫ p j ≫
          superBiproductι (K := K) T j) ≫
        superBiproductπ (K := K) T j := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [Category.assoc, Category.assoc,
          superBiproductι_π_ne T hkj, comp_zero, comp_zero]
      · simp
    _ = _ := by
      rw [Category.assoc, Category.assoc,
        superBiproductι_π_self, Category.comp_id]

/-- A diagonal extension of common degree `d` has degree `d`. -/
theorem superBiproductMap_mem
    (S T : J → C) (p : ∀ j, S j ⟶ T j) (d : ZMod 2)
    (hp : ∀ j, p j ∈ homGrade K (S j) (T j) d) :
    superBiproductMap (K := K) S T p ∈
      homGrade K
        (superBiproduct (K := K) S)
        (superBiproduct (K := K) T) d := by
  classical
  rw [superBiproductMap]
  apply Submodule.sum_mem
  intro j _
  have h₁ := Supercategory.comp_mem
    (superBiproductπ (K := K) S j) (p j)
    (superBiproductπ_mem (K := K) S j) (hp j)
  have h₂ := Supercategory.comp_mem
    (superBiproductπ (K := K) S j ≫ p j)
    (superBiproductι (K := K) T j) h₁
    (superBiproductι_mem (K := K) T j)
  change _ ∈ Supercategory.grade
    (superBiproduct (K := K) S) (superBiproduct (K := K) T) d
  simpa only [zero_add, add_zero, Category.assoc] using h₂

/-- Diagonal extension is additive in its component maps. -/
theorem superBiproductMap_add
    (S T : J → C) (p q : ∀ j, S j ⟶ T j) :
    superBiproductMap (K := K) S T (fun j => p j + q j) =
      superBiproductMap (K := K) S T p +
        superBiproductMap (K := K) S T q := by
  classical
  rw [superBiproductMap, superBiproductMap, superBiproductMap]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Preadditive.add_comp, Preadditive.comp_add]

/-- Diagonal extension is `K`-linear in its component maps. -/
theorem superBiproductMap_smul
    (S T : J → C) (c : K) (p : ∀ j, S j ⟶ T j) :
    superBiproductMap (K := K) S T (fun j => c • p j) =
      c • superBiproductMap (K := K) S T p := by
  classical
  rw [superBiproductMap, superBiproductMap]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Linear.smul_comp, Linear.comp_smul]

/-- Diagonal extension preserves componentwise composition. -/
@[simp]
theorem superBiproductMap_comp
    (S T U : J → C)
    (p : ∀ j, S j ⟶ T j) (q : ∀ j, T j ⟶ U j) :
    superBiproductMap (K := K) S T p ≫
        superBiproductMap (K := K) T U q =
      superBiproductMap (K := K) S U (fun j => p j ≫ q j) := by
  apply superBiproduct_hom_ext (K := K) S
  intro j
  rw [← Category.assoc, superBiproductι_map, Category.assoc,
    superBiproductι_map, superBiproductι_map]
  exact (Category.assoc (p j) (q j)
    (superBiproductι (K := K) U j)).symm

/-- A common componentwise scalar in a diagonal composition factors out
of the finite super-biproduct map. -/
theorem superBiproductMap_comp_of_pointwise_smul
    (S T U : J → C)
    (p : ∀ j, S j ⟶ T j) (q : ∀ j, T j ⟶ U j)
    (r : ∀ j, S j ⟶ U j) (c : K)
    (h : ∀ j, p j ≫ q j = c • r j) :
    superBiproductMap (K := K) S T p ≫
        superBiproductMap (K := K) T U q =
      c • superBiproductMap (K := K) S U r := by
  rw [superBiproductMap_comp]
  calc
    superBiproductMap (K := K) S U (fun j => p j ≫ q j) =
        superBiproductMap (K := K) S U (fun j => c • r j) := by
      congr 1
      funext j
      exact h j
    _ = _ := superBiproductMap_smul (K := K) S U c r

/-- Diagonal extension preserves identity maps. -/
@[simp]
theorem superBiproductMap_id (S : J → C) :
    superBiproductMap (K := K) S S (fun j => 𝟙 (S j)) =
      𝟙 (superBiproduct (K := K) S) := by
  classical
  rw [superBiproductMap]
  simpa only [Category.id_comp] using superBiproduct_total (K := K) S

/-- A finite super-biproduct supported at one selected index is evenly
isomorphic to its selected summand.

The hypotheses assert only that every off-selected summand is a zero
object.  The forward and inverse maps are the chosen projection and
inclusion, so this construction introduces no auxiliary choices. -/
noncomputable def superBiproductSingleSupportEvenIso
    (S : J → C) (j : J)
    (hS : ∀ k, k ≠ j → IsZero (S k)) :
    EvenIso K (superBiproduct (K := K) S) (S j) where
  iso :=
    { hom := superBiproductπ (K := K) S j
      inv := superBiproductι (K := K) S j
      hom_inv_id := by
        rw [← superBiproduct_total (K := K) S]
        symm
        apply Finset.sum_eq_single j
        · intro k _ hkj
          rw [(hS k hkj).eq_of_tgt
            (superBiproductπ (K := K) S k), zero_comp]
        · simp
      inv_hom_id := superBiproductι_π_self (K := K) S j }
  hom_mem := superBiproductπ_mem (K := K) S j
  inv_mem := superBiproductι_mem (K := K) S j

/-- The forward map of the single-support equivalence is the selected
super-biproduct projection. -/
@[simp]
theorem superBiproductSingleSupportEvenIso_hom
    (S : J → C) (j : J)
    (hS : ∀ k, k ≠ j → IsZero (S k)) :
    (superBiproductSingleSupportEvenIso (K := K) S j hS).iso.hom =
      superBiproductπ (K := K) S j :=
  rfl

/-- The inverse map of the single-support equivalence is the selected
super-biproduct inclusion. -/
@[simp]
theorem superBiproductSingleSupportEvenIso_inv
    (S : J → C) (j : J)
    (hS : ∀ k, k ≠ j → IsZero (S k)) :
    (superBiproductSingleSupportEvenIso (K := K) S j hS).iso.inv =
      superBiproductι (K := K) S j :=
  rfl

/-- The forward single-support equivalences intertwine a diagonal
super-biproduct map with its selected component. -/
@[reassoc]
theorem superBiproductSingleSupportEvenIso_hom_naturality
    (S T : J → C) (j : J)
    (hS : ∀ k, k ≠ j → IsZero (S k))
    (hT : ∀ k, k ≠ j → IsZero (T k))
    (p : ∀ k, S k ⟶ T k) :
    superBiproductMap (K := K) S T p ≫
        (superBiproductSingleSupportEvenIso (K := K) T j hT).iso.hom =
      (superBiproductSingleSupportEvenIso (K := K) S j hS).iso.hom ≫
        p j := by
  rw [superBiproductSingleSupportEvenIso_hom,
    superBiproductSingleSupportEvenIso_hom, superBiproductMap_π]

end

end Superfusion.Category
