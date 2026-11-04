import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Simple

/-! Finite sums of simple objects with Schur's property have split images.
Gaussian elimination isolates a nonzero simple matrix coefficient at each step. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped ZeroObject
universe u v
namespace RMod.EnrichedSupport
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A morphism factors through an object by a split epimorphism and a split monomorphism. -/
def HasSplitImage {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ (I : C) (p : X ⟶ I) (i : I ⟶ Y) (s : I ⟶ X) (r : Y ⟶ I),
    s ≫ p = 𝟙 I ∧ i ≫ r = 𝟙 I ∧ p ≫ i = f

namespace HasSplitImage

theorem of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : HasSplitImage f :=
  ⟨Y, f, 𝟙 Y, inv f, 𝟙 Y, by simp, by simp, by simp⟩

theorem zero [HasZeroObject C] (X Y : C) : HasSplitImage (0 : X ⟶ Y) :=
  ⟨0, 0, 0, 0, 0, by simp, by simp, by simp⟩

theorem transport {X Y X' Y' : C} {f : X ⟶ Y} (hf : HasSplitImage f)
    (e : X' ≅ X) (d : Y ≅ Y') : HasSplitImage (e.hom ≫ f ≫ d.hom) := by
  obtain ⟨I, p, i, s, r, hp, hi, h⟩ := hf
  exact ⟨I, e.hom ≫ p, i ≫ d.hom, s ≫ e.inv, d.inv ≫ r,
    by simp [Category.assoc, hp], by simp [Category.assoc, hi], by simp [← h, Category.assoc]⟩

theorem pre_split {X Y Z : C} {f : X ⟶ Y} (hf : HasSplitImage f)
    (q : Z ⟶ X) (t : X ⟶ Z) (ht : t ≫ q = 𝟙 X) : HasSplitImage (q ≫ f) := by
  obtain ⟨I, p, i, s, r, hp, hi, h⟩ := hf
  exact ⟨I, q ≫ p, i, s ≫ t, r, by rw [Category.assoc, ← Category.assoc t q p, ht, Category.id_comp, hp], hi,
    by simp [← h, Category.assoc]⟩

theorem map [HasBinaryBiproducts C] {X₁ X₂ Y₁ Y₂ : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} (hf : HasSplitImage f) (hg : HasSplitImage g) :
    HasSplitImage (biprod.map f g) := by
  obtain ⟨I, p, i, s, r, hp, hi, h⟩ := hf
  obtain ⟨J, q, j, t, z, hq, hj, h'⟩ := hg
  exact ⟨I ⊞ J, biprod.map p q, biprod.map i j, biprod.map s t, biprod.map r z,
    by apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [Category.assoc, hp, hq], by apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [Category.assoc, hi, hj],
    by apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [Category.assoc, h, h']⟩
end HasSplitImage

variable [HasFiniteBiproducts C]

/-- Split the first term from a finite biproduct. -/
def biproductFinSuccIso {n : ℕ} (S : Fin (n + 1) → C) :
    (⨁ S) ≅ S 0 ⊞ ⨁ (fun i : Fin n => S i.succ) where
  hom := biprod.lift (biproduct.π S 0) (biproduct.lift fun i => biproduct.π S i.succ)
  inv := biprod.desc (biproduct.ι S 0) (biproduct.desc fun i => biproduct.ι S i.succ)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hz : biproduct.ι S 0 ≫ (biproduct.lift fun i : Fin n => biproduct.π S i.succ) = 0 := by
        apply biproduct.hom_ext
        intro k
        simp [biproduct.ι_π, Ne.symm (Fin.succ_ne_zero k)]
      simpa [← Category.assoc, hz]
    · have hj : biproduct.ι S j.succ ≫ (biproduct.lift fun i : Fin n => biproduct.π S i.succ) =
          biproduct.ι (fun i : Fin n => S i.succ) j := by
        apply biproduct.hom_ext
        intro k
        by_cases h : j = k
        · subst k; simp
        · simp [biproduct.ι_π, h]
      simpa [← Category.assoc, hj]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext
      intro i
      simp [biproduct.ι_π, Ne.symm (Fin.succ_ne_zero i)]
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro i
      apply biproduct.hom_ext
      intro j
      by_cases h : i = j
      · subst j; simp
      · simp [biproduct.ι_π, h]

/-- A selected summand and all remaining summands give a binary biproduct. -/
def biproductSplitIso {J : Type} [Fintype J] (S : J → C) (j : J) :
    (⨁ S) ≅ S j ⊞ ⨁ (Subtype.restrict (fun k => k ≠ j) S) where
  hom := biprod.lift (biproduct.π S j) (biproduct.toSubtype S (fun k => k ≠ j))
  inv := biprod.desc (biproduct.ι S j) (biproduct.fromSubtype S (fun k => k ≠ j))
  hom_inv_id := by
    classical
    apply biproduct.hom_ext'
    intro k
    by_cases h : k = j
    · subst k
      have hz : biproduct.ι S j ≫ biproduct.toSubtype S (fun k => k ≠ j) = 0 := by
        apply biproduct.hom_ext
        intro k
        simp [biproduct.toSubtype, biproduct.ι_π, Ne.symm k.property]
      simpa [← Category.assoc, hz]
    · simp [biproduct.ι_toSubtype, h]
  inv_hom_id := by
    classical
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext
      intro k
      simp [biproduct.toSubtype, Ne.symm k.property]
    · apply biproduct.hom_ext'
      intro k
      simp [biproduct.fromSubtype, k.property]
    · simp

@[simp] theorem biproductSplitIso_hom_fst {J : Type} [Fintype J] (S : J → C) (j : J) :
    (biproductSplitIso S j).hom ≫ biprod.fst = biproduct.π S j := by
  simp [biproductSplitIso]

/-- Gaussian elimination gives split images for a finite sum of simple objects. -/
theorem finite_split_image
    (hsemi : ∀ Y : C, ∃ (m : ℕ) (T : Fin m → C),
      (∀ j, Simple (T j)) ∧ Nonempty (Y ≅ ⨁ T))
    (hSchur : ∀ (S T : C), Simple S → Simple T → ∀ (f : S ⟶ T), f ≠ 0 → IsIso f)
    (n : ℕ) : ∀ (S : Fin n → C), (∀ i, Simple (S i)) →
      ∀ (Y : C) (f : (⨁ S) ⟶ Y), HasSplitImage f := by
  classical
  induction n with
  | zero =>
      intro S hS Y f
      have hf : f = 0 := by
        apply biproduct.hom_ext'
        intro i
        exact Fin.elim0 i
      rw [hf]
      exact HasSplitImage.zero _ _
  | succ n ih =>
      intro S hS Y f
      let e := biproductFinSuccIso S
      let f' := e.inv ≫ f
      let g := biprod.inr ≫ f'
      by_cases hz : (biprod.inl : S 0 ⟶ S 0 ⊞ ⨁ (fun i : Fin n => S i.succ)) ≫ f' = 0
      · have hg := (ih (fun i => S i.succ) (fun i => hS i.succ) Y g).pre_split
          (biprod.snd : S 0 ⊞ (⨁ fun i : Fin n => S i.succ) ⟶ _) biprod.inr (by simp)
        have hf' : f' = biprod.snd ≫ g := by
          apply biprod.hom_ext' <;> simp [hz, g]
        rw [← hf'] at hg
        simpa [f', Category.assoc] using hg.transport e (Iso.refl Y)
      · obtain ⟨m, T, hT, ⟨d⟩⟩ := hsemi Y
        have hex : ∃ j, biprod.inl ≫ f' ≫ d.hom ≫ biproduct.π T j ≠ 0 := by
          by_contra! hn
          apply hz
          apply (cancel_mono d.hom).1
          have hh : biprod.inl ≫ f' ≫ d.hom = 0 := by
            apply biproduct.hom_ext
            intro j
            simpa [Category.assoc] using hn j
          simpa [Category.assoc] using hh
        obtain ⟨j, hj⟩ := hex
        let q := biproductSplitIso T j
        let F := f' ≫ d.hom ≫ q.hom
        have ha : biprod.inl ≫ F ≫ biprod.fst ≠ 0 := by
          simpa [F, q, Category.assoc] using hj
        letI : IsIso (biprod.inl ≫ F ≫ biprod.fst) :=
          hSchur (S 0) (T j) (hS 0) (hT j) _ ha
        obtain ⟨L, R, k, hk⟩ := Biprod.gaussian F
        have hm : HasSplitImage (L.hom ≫ F ≫ R.hom) := by
          rw [hk]
          exact (HasSplitImage.of_isIso _).map
            (ih (fun i => S i.succ) (fun i => hS i.succ) _ k)
        have hF : HasSplitImage F := by
          simpa [Category.assoc] using hm.transport L.symm R.symm
        simpa [F, f', Category.assoc] using hF.transport e (q.symm.trans d.symm)

/-- Every morphism in a finite semisimple category with Schur's property has a split image. -/
theorem split_images_of_semisimple
    (hsemi : ∀ Y : C, ∃ (m : ℕ) (T : Fin m → C),
      (∀ j, Simple (T j)) ∧ Nonempty (Y ≅ ⨁ T))
    (hSchur : ∀ (S T : C), Simple S → Simple T → ∀ (f : S ⟶ T), f ≠ 0 → IsIso f)
    {X Y : C} (f : X ⟶ Y) : HasSplitImage f := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := hsemi X
  have hf := finite_split_image hsemi hSchur n S hS Y (e.inv ≫ f)
  simpa [Category.assoc] using hf.transport e (Iso.refl Y)

end RMod.EnrichedSupport
