/-
Superfusion / Super / GradedTransfer

Transport of the superalgebra mixins along a grading-preserving algebra
equivalence: if `φ : A ≃ₐ[K] B` carries `𝒜 i` onto `ℬ i`, then

* graded components transport (`evenPart_map`, `oddPart_map`,
  `decompose_map`),
* `IsSuperCentral 𝒜 → IsSuperCentral ℬ`,
* `IsGradedSimple 𝒜 → IsGradedSimple ℬ`.

This is the glue that lets the explicit models (M7a: `AdjoinOdd`)
equip mathlib's own algebras (Clifford algebras with the `evenOdd`
grading, M7b) with central simplicity, and later transports along
`CliffordAlgebra.prodEquiv` and the graded-tensor braiding (M7c).
-/
import Superfusion.Super.RegularSchur
import Superfusion.Super.ParityInvolution
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

namespace Superfusion

section Equiv

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable (φ : A ≃ₐ[K] B) (hφ : ∀ i, (𝒜 i).map φ.toLinearMap = ℬ i)

include φ hφ

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- Membership transport along a grading-preserving equivalence. -/
theorem mem_iff_map_mem {i : ZMod 2} {x : A} : x ∈ 𝒜 i ↔ φ x ∈ ℬ i := by
  rw [← hφ i, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := φ.injective (by simpa using hyx)
    exact hxy ▸ hy

/-- The even projection commutes with a grading-preserving equivalence. -/
theorem evenPart_map (x : A) : evenPart ℬ (φ x) = φ (evenPart 𝒜 x) := by
  have hsplit : φ x = φ (evenPart 𝒜 x) + φ (oddPart 𝒜 x) := by
    rw [← map_add, evenPart_add_oddPart]
  have h0 : φ (evenPart 𝒜 x) ∈ ℬ 0 :=
    (mem_iff_map_mem 𝒜 ℬ φ hφ).mp (evenPart_mem 𝒜 x)
  have h1 : φ (oddPart 𝒜 x) ∈ ℬ 1 :=
    (mem_iff_map_mem 𝒜 ℬ φ hφ).mp (oddPart_mem 𝒜 x)
  rw [hsplit, map_add, evenPart_of_mem_zero ℬ h0, evenPart_of_mem_one ℬ h1,
    add_zero]

/-- The odd projection commutes with a grading-preserving equivalence. -/
theorem oddPart_map (x : A) : oddPart ℬ (φ x) = φ (oddPart 𝒜 x) := by
  have hsplit : φ x = φ (evenPart 𝒜 x) + φ (oddPart 𝒜 x) := by
    rw [← map_add, evenPart_add_oddPart]
  have h0 : φ (evenPart 𝒜 x) ∈ ℬ 0 :=
    (mem_iff_map_mem 𝒜 ℬ φ hφ).mp (evenPart_mem 𝒜 x)
  have h1 : φ (oddPart 𝒜 x) ∈ ℬ 1 :=
    (mem_iff_map_mem 𝒜 ℬ φ hφ).mp (oddPart_mem 𝒜 x)
  rw [hsplit, map_add, oddPart_of_mem_zero ℬ h0, oddPart_of_mem_one ℬ h1,
    zero_add]

/-- Graded components commute with a grading-preserving equivalence. -/
theorem decompose_map (x : A) (i : ZMod 2) :
    ((DirectSum.decompose ℬ (φ x) i : ℬ i) : B) =
      φ ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A) := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact evenPart_map 𝒜 ℬ φ hφ x
  · exact oddPart_map 𝒜 ℬ φ hφ x

/-- The parity involution commutes with a grading-preserving
equivalence. -/
theorem parityMap_map (x : A) :
    parityMap ℬ (φ x) = φ (parityMap 𝒜 x) := by
  rw [parityMap_apply, evenPart_map 𝒜 ℬ φ hφ, oddPart_map 𝒜 ℬ φ hφ,
    ← map_sub, ← parityMap_apply]

/-- Supercentrality transports along a grading-preserving equivalence. -/
theorem isSuperCentral_of_equiv [IsSuperCentral 𝒜] : IsSuperCentral ℬ := by
  constructor
  have layer : ∀ i : ZMod 2, superCenterGrade ℬ i ≤ (1 : Submodule K B) := by
    rintro i z ⟨hz, hzc⟩
    have hzw : φ (φ.symm z) = z := φ.apply_symm_apply z
    have hwmem : φ.symm z ∈ 𝒜 i := by
      rw [mem_iff_map_mem 𝒜 ℬ φ hφ, hzw]
      exact hz
    have hwc : IsSupercentral 𝒜 i (φ.symm z) := by
      intro j b hb
      apply φ.injective
      rw [map_mul, map_zsmul, map_mul, hzw]
      exact hzc j (φ b) ((mem_iff_map_mem 𝒜 ℬ φ hφ).mp hb)
    have hw1 : φ.symm z ∈ (1 : Submodule K A) := by
      refine IsSuperCentral.superCenter_le_one (𝒜 := 𝒜) ?_
      rcases zmod2_cases i with hi | hi <;> subst hi
      · exact le_sup_left (α := Submodule K A) ⟨hwmem, hwc⟩
      · exact le_sup_right (α := Submodule K A) ⟨hwmem, hwc⟩
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hw1
    refine Submodule.mem_one.mpr ⟨c, ?_⟩
    rw [← hzw, ← hc, AlgEquiv.commutes]
  rw [superCenter, sup_le_iff]
  exact ⟨layer 0, layer 1⟩

/-- Graded simplicity transports along a grading-preserving equivalence. -/
theorem isGradedSimple_of_equiv [IsGradedSimple 𝒜] : IsGradedSimple ℬ := by
  constructor
  intro I hI
  set J : TwoSidedIdeal A := TwoSidedIdeal.mk' (φ ⁻¹' I)
    (by simp only [Set.mem_preimage, map_zero]; exact I.zero_mem)
    (fun hx hy => by
      simp only [Set.mem_preimage, map_add] at *
      exact I.add_mem hx hy)
    (fun hx => by
      simp only [Set.mem_preimage, map_neg] at *
      exact I.neg_mem hx)
    (fun {x y} hy => by
      simp only [Set.mem_preimage, map_mul] at *
      exact I.mul_mem_left _ _ hy)
    (fun {x y} hx => by
      simp only [Set.mem_preimage, map_mul] at *
      exact I.mul_mem_right _ _ hx) with hJdef
  have memJ : ∀ x : A, x ∈ J ↔ φ x ∈ I := by
    intro x
    rw [hJdef, TwoSidedIdeal.mem_mk', Set.mem_preimage]
    rfl
  have hJ : TwoSidedIdeal.IsHomogeneous 𝒜 J := by
    intro a ha i
    rw [memJ]
    have := hI (φ a) ((memJ a).mp ha) i
    rwa [decompose_map 𝒜 ℬ φ hφ] at this
  rcases IsGradedSimple.eq_bot_or_eq_top J hJ with h | h
  · left
    refine SetLike.ext fun y => ?_
    rw [TwoSidedIdeal.mem_bot B]
    constructor
    · intro hy
      have hmem : φ.symm y ∈ J := by
        rw [memJ, φ.apply_symm_apply]
        exact hy
      rw [h, TwoSidedIdeal.mem_bot A] at hmem
      calc y = φ (φ.symm y) := (φ.apply_symm_apply y).symm
        _ = φ 0 := by rw [hmem]
        _ = 0 := map_zero φ
    · rintro rfl
      exact I.zero_mem
  · right
    refine SetLike.ext fun y => ?_
    refine ⟨fun _ => TwoSidedIdeal.mem_top B, fun _ => ?_⟩
    have hmem : φ.symm y ∈ J := h ▸ TwoSidedIdeal.mem_top A
    rw [memJ, φ.apply_symm_apply] at hmem
    exact hmem


end Equiv

/-! ### Homogeneous homomorphisms: graded components and injectivity -/

section Hom

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable (𝒜 : ZMod 2 → Submodule K A) (ℬ : ZMod 2 → Submodule K B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
variable (φ : A →ₐ[K] B) (hφ : ∀ i, ∀ x ∈ 𝒜 i, φ x ∈ ℬ i)

include hφ

/-- The even projection commutes with a grade-preserving homomorphism
(no injectivity needed). -/
theorem evenPart_map_of_isHomogeneous (x : A) :
    evenPart ℬ (φ x) = φ (evenPart 𝒜 x) := by
  have hsplit : φ x = φ (evenPart 𝒜 x) + φ (oddPart 𝒜 x) := by
    rw [← map_add, evenPart_add_oddPart]
  have h0 : φ (evenPart 𝒜 x) ∈ ℬ 0 := hφ 0 _ (evenPart_mem 𝒜 x)
  have h1 : φ (oddPart 𝒜 x) ∈ ℬ 1 := hφ 1 _ (oddPart_mem 𝒜 x)
  rw [hsplit, map_add, evenPart_of_mem_zero ℬ h0, evenPart_of_mem_one ℬ h1,
    add_zero]

/-- The odd projection commutes with a grade-preserving homomorphism. -/
theorem oddPart_map_of_isHomogeneous (x : A) :
    oddPart ℬ (φ x) = φ (oddPart 𝒜 x) := by
  have hsplit : φ x = φ (evenPart 𝒜 x) + φ (oddPart 𝒜 x) := by
    rw [← map_add, evenPart_add_oddPart]
  have h0 : φ (evenPart 𝒜 x) ∈ ℬ 0 := hφ 0 _ (evenPart_mem 𝒜 x)
  have h1 : φ (oddPart 𝒜 x) ∈ ℬ 1 := hφ 1 _ (oddPart_mem 𝒜 x)
  rw [hsplit, map_add, oddPart_of_mem_zero ℬ h0, oddPart_of_mem_one ℬ h1,
    zero_add]

/-- Graded components commute with a grade-preserving homomorphism. -/
theorem decompose_map_of_isHomogeneous (x : A) (i : ZMod 2) :
    ((DirectSum.decompose ℬ (φ x) i : ℬ i) : B) =
      φ ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A) := by
  rcases zmod2_cases i with hi | hi <;> subst hi
  · exact evenPart_map_of_isHomogeneous 𝒜 ℬ φ hφ x
  · exact oddPart_map_of_isHomogeneous 𝒜 ℬ φ hφ x

/-- A grade-preserving homomorphism out of a graded-simple superalgebra
into a nontrivial one is injective: its kernel is a homogeneous
two-sided ideal. -/
theorem injective_of_isGradedSimple [IsGradedSimple 𝒜] [Nontrivial B] :
    Function.Injective φ := by
  suffices h : ∀ z : A, φ z = 0 → z = 0 by
    intro x y hxy
    have := h (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  intro z hz
  have hI : TwoSidedIdeal.IsHomogeneous 𝒜 (TwoSidedIdeal.ker φ) := by
    intro a ha i
    rw [TwoSidedIdeal.mem_ker] at ha ⊢
    rw [← decompose_map_of_isHomogeneous 𝒜 ℬ φ hφ, ha]
    simp
  rcases IsGradedSimple.eq_bot_or_eq_top (TwoSidedIdeal.ker φ) hI with h | h
  · have hzmem : z ∈ TwoSidedIdeal.ker φ := (TwoSidedIdeal.mem_ker φ).mpr hz
    rw [h, TwoSidedIdeal.mem_bot A] at hzmem
    exact hzmem
  · exfalso
    have h1 : (1 : A) ∈ TwoSidedIdeal.ker φ := h ▸ TwoSidedIdeal.mem_top A
    rw [TwoSidedIdeal.mem_ker, map_one] at h1
    exact one_ne_zero h1

/-- A bijective grade-preserving homomorphism carries the grading onto
the grading: the forward inclusion is the hypothesis, and the reverse
follows from uniqueness of decompositions plus injectivity. -/
theorem map_grading_of_bijective (hbij : Function.Bijective φ)
    (i : ZMod 2) : (𝒜 i).map φ.toLinearMap = ℬ i := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact hφ i x hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    have h0 : φ (evenPart 𝒜 x) ∈ ℬ 0 := hφ 0 _ (evenPart_mem 𝒜 x)
    have h1 : φ (oddPart 𝒜 x) ∈ ℬ 1 := hφ 1 _ (oddPart_mem 𝒜 x)
    rcases zmod2_cases i with hi | hi <;> subst hi
    · have hde := DirectSum.decompose_of_mem_ne ℬ hy
        (by decide : (0 : ZMod 2) ≠ 1)
      rw [decompose_map_of_isHomogeneous 𝒜 ℬ φ hφ] at hde
      have hx1 : oddPart 𝒜 x = 0 := hbij.1 (by rw [map_zero]; exact hde)
      have hxe : x = evenPart 𝒜 x := by
        conv_lhs => rw [← evenPart_add_oddPart 𝒜 x]
        rw [hx1, add_zero]
      exact Submodule.mem_map.mpr ⟨evenPart 𝒜 x, evenPart_mem 𝒜 x,
        by rw [AlgHom.toLinearMap_apply, ← hxe]⟩
    · have hde := DirectSum.decompose_of_mem_ne ℬ hy
        (by decide : (1 : ZMod 2) ≠ 0)
      rw [decompose_map_of_isHomogeneous 𝒜 ℬ φ hφ] at hde
      have hx0 : evenPart 𝒜 x = 0 := hbij.1 (by rw [map_zero]; exact hde)
      have hxo : x = oddPart 𝒜 x := by
        conv_lhs => rw [← evenPart_add_oddPart 𝒜 x]
        rw [hx0, zero_add]
      exact Submodule.mem_map.mpr ⟨oddPart 𝒜 x, oddPart_mem 𝒜 x,
        by rw [AlgHom.toLinearMap_apply, ← hxo]⟩

end Hom

end Superfusion
