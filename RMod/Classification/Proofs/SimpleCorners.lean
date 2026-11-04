import RMod.Classification.Proofs.SimpleSplitting

/-!
# Even idempotents in a simple retract corner

An even nonzero idempotent of a simple object is invertible by graded
Schur and therefore is the identity. Compressing an idempotent supported
in a simple retract to that simple object shows that it is either zero
or the whole retract projector. This will split transported primitive
projectors without assuming idempotent completeness as an extra law.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End

variable (C : WeaklyPointedSuperfusion.{0, 0})

theorem simple_even_idempotent_eq_id {S : LinearCategory C} (hS : C.data.IsSimple S)
    (q : End S) (hq : C.data.IsHomogeneous 0 q) (hqq : q ≫ q = q) (hne : q ≠ 0) : q = 𝟙 S := by
  obtain ⟨r, hqr, _⟩ := C.laws.graded_schur hS hS q hq hne
  let r' : S ⟶ S := r
  have hqr' : q ≫ r' = 𝟙 S := hqr
  calc
    q = q ≫ (q ≫ r') := by rw [hqr', Category.comp_id]
    _ = q ≫ r' := by rw [← Category.assoc, hqq]
    _ = 𝟙 S := hqr'

theorem simple_retract_idempotent_unique {S X : LinearCategory C} (hS : C.data.IsSimple S)
    (i : S ⟶ X) (p : X ⟶ S)
    (hi : C.data.IsHomogeneous 0 i) (hp : C.data.IsHomogeneous 0 p)
    (q : End X) (hq : C.data.IsHomogeneous 0 q) (hqq : q ≫ q = q) (hne : q ≠ 0)
    (hqe : q ≫ (p ≫ i) = q) (heq : (p ≫ i) ≫ q = q) : q = p ≫ i := by
  let k : End S := i ≫ q ≫ p
  have hk : C.data.IsHomogeneous 0 k := by
    have h := C.laws.comp_grade _ _ hi (C.laws.comp_grade _ _ hq hp)
    simp only [zero_add] at h
    exact h
  have hrecover : p ≫ k ≫ i = q := by
    change p ≫ (i ≫ q ≫ p) ≫ i = q
    calc
      _ = ((p ≫ i) ≫ q) ≫ (p ≫ i) := by simp only [Category.assoc]
      _ = q := by rw [heq, hqe]
  have hkn : k ≠ 0 := by
    intro hz
    apply hne
    rw [← hrecover, hz]
    change C.data.comp p (C.data.comp C.data.zero i) = C.data.zero
    rw [raw_zero_comp C.laws, raw_comp_zero C.laws]
  have hkk : k ≫ k = k := by
    change (i ≫ q ≫ p) ≫ (i ≫ q ≫ p) = i ≫ q ≫ p
    calc
      _ = i ≫ (q ≫ (p ≫ i)) ≫ q ≫ p := by simp only [Category.assoc]
      _ = i ≫ (q ≫ q) ≫ p := by rw [hqe]; simp only [Category.assoc]
      _ = _ := by rw [hqq]
  have hid := simple_even_idempotent_eq_id C hS k hk hkk hkn
  calc
    q = p ≫ k ≫ i := hrecover.symm
    _ = p ≫ i := by rw [hid, Category.id_comp]

end RMod.Classification
