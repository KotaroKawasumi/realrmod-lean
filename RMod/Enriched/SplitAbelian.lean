import RMod.Enriched.SplitImages
import Mathlib.CategoryTheory.Idempotents.Basic

/-! Split images supply kernels, cokernels, and an abelian structure without
adding Schur or abelianity as a new assumption on the existing models. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
universe u v
namespace RMod.EnrichedSupport
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A split-image factorization of an idempotent is a splitting of that idempotent. -/
theorem split_idempotent
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), HasSplitImage f)
    {X : C} (e : X ⟶ X) (he : e ≫ e = e) :
    ∃ (I : C) (i : I ⟶ X) (p : X ⟶ I), i ≫ p = 𝟙 I ∧ p ≫ i = e := by
  obtain ⟨I, p, i, s, r, hp, hi, hf⟩ := h e
  haveI : Epi p := SplitEpi.epi ⟨s, hp⟩
  haveI : Mono i := SplitMono.mono ⟨r, hi⟩
  refine ⟨I, i, p, ?_, hf⟩
  apply (cancel_epi p).1
  apply (cancel_mono i).1
  simpa [← hf, Category.assoc] using he

/-- Complements of the two split-image projectors give the kernel and cokernel. -/
theorem hasAbelianStruct_of_split_images
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), HasSplitImage f)
    {X Y : C} (f : X ⟶ Y) : Nonempty (Abelian.AbelianStruct f) := by
  obtain ⟨I, p, i, s, r, hp, hi, hf⟩ := h f
  haveI : Epi p := SplitEpi.epi ⟨s, hp⟩
  haveI : Mono i := SplitMono.mono ⟨r, hi⟩
  obtain ⟨K, k, l, hkl, hlk⟩ := split_idempotent h (𝟙 X - p ≫ s)
    (Idempotents.idem_of_id_sub_idem _ (by rw [Category.assoc, ← Category.assoc s p s, hp, Category.id_comp]))
  obtain ⟨Q, j, q, hjq, hqj⟩ := split_idempotent h (𝟙 Y - r ≫ i)
    (Idempotents.idem_of_id_sub_idem _ (by rw [Category.assoc, ← Category.assoc i r i, hi, Category.id_comp]))
  haveI : Mono k := SplitMono.mono ⟨l, hkl⟩
  haveI : Epi q := SplitEpi.epi ⟨j, hjq⟩
  haveI : Mono j := SplitMono.mono ⟨q, hjq⟩
  have hkp : k ≫ p = 0 := by
    calc
      k ≫ p = k ≫ (l ≫ k) ≫ p := by simp [← Category.assoc, hkl]
      _ = k ≫ (𝟙 X - p ≫ s) ≫ p := by rw [hlk]
      _ = 0 := by simp [sub_comp, comp_sub, Category.assoc, hp]
  have hiq : i ≫ q = 0 := by
    apply (cancel_mono j).1
    simp only [Category.assoc, hqj, comp_sub, Category.comp_id]
    simp [← Category.assoc, hi]
  have hk : IsLimit (KernelFork.ofι k hkp) := by
    apply KernelFork.IsLimit.ofι'
    intro Z a ha
    refine ⟨a ≫ l, ?_⟩
    rw [Category.assoc, hlk, comp_sub, Category.comp_id]
    simp [← Category.assoc, ha]
  have hq : IsColimit (CokernelCofork.ofπ q hiq) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro Z a ha
    refine ⟨j ≫ a, ?_⟩
    rw [← Category.assoc, hqj, sub_comp, Category.id_comp]
    simp [Category.assoc, ha]
  have hp' : IsColimit (CokernelCofork.ofπ p hkp) := by
    apply CokernelCofork.IsColimit.ofπ'
    intro Z a ha
    refine ⟨s ≫ a, ?_⟩
    have hz : (𝟙 X - p ≫ s) ≫ a = 0 := by
      rw [← hlk, Category.assoc, ha, comp_zero]
    have hh : a - (p ≫ s) ≫ a = 0 := by simpa [sub_comp] using hz
    exact (Category.assoc _ _ _).symm.trans (sub_eq_zero.mp hh).symm
  have hi' : IsLimit (KernelFork.ofι i hiq) := by
    apply KernelFork.IsLimit.ofι'
    intro Z a ha
    refine ⟨a ≫ r, ?_⟩
    have hz : a ≫ (𝟙 Y - r ≫ i) = 0 := by
      rw [← hqj, ← Category.assoc, ha, zero_comp]
    have hh : a - a ≫ r ≫ i = 0 := by simpa [comp_sub] using hz
    exact (Category.assoc _ _ _).trans (sub_eq_zero.mp hh).symm
  exact ⟨{
    kernelFork := KernelFork.ofι k (by rw [← hf, ← Category.assoc, hkp, zero_comp])
    isLimitKernelFork := isKernelCompMono hk i hf.symm
    cokernelCofork := CokernelCofork.ofπ q (by rw [← hf, Category.assoc, hiq, comp_zero])
    isColimitCokernelCofork := isCokernelEpiComp hq p hf.symm
    image := I
    imageπ := p
    ι_imageπ := hkp
    imageIsCokernel := hp'
    imageι := i
    imageι_π := hiq
    imageIsKernel := hi'
    fac := hf }⟩

/-- The abelian structure is constructed from finite products and split images. -/
@[implicit_reducible] def abelianOfSplitImages [HasFiniteProducts C]
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), HasSplitImage f) : Abelian C :=
  Abelian.mk' (fun {_ _} f => hasAbelianStruct_of_split_images h f)

/-- Finite semisimplicity and Schur's property imply abelianity. -/
@[implicit_reducible] def abelianOfSemisimple [HasFiniteBiproducts C]
    (hsemi : ∀ Y : C, ∃ (m : ℕ) (T : Fin m → C),
      (∀ j, Simple (T j)) ∧ Nonempty (Y ≅ ⨁ T))
    (hSchur : ∀ (S T : C), Simple S → Simple T → ∀ (f : S ⟶ T), f ≠ 0 → IsIso f) :
    Abelian C :=
  abelianOfSplitImages (fun {_ _} f => split_images_of_semisimple hsemi hSchur f)

end RMod.EnrichedSupport
