import RMod.Hierarchy.Bridge.LegacyEven

/-!
# Finiteness and semisimplicity for the extracted operations

Mathlib biproducts supply the raw matrix identities, and finite bases
supply the legacy coordinate witnesses. All witnesses here are used only
inside the proposition-valued legacy laws.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace RMod.Legacy.Hierarchy
variable (C : MonoidalSupercategory)

theorem legacy_finSum {X Y : TotalCategory C.super} (n : ℕ)
    (f : Fin n → (X ⟶ Y)) :
    (toOldData C).finSum n f = ∑ i, f i := by
  induction n with
  | zero => simp [WeaklyPointedSuperfusionData.finSum]; rfl
  | succ n ih =>
    rw [WeaklyPointedSuperfusionData.finSum, Fin.sum_univ_castSucc, ih]
    rfl

theorem legacyDecomposition [HasFiniteBiproducts (Even C.super)]
    (X : Even C.super) {n : ℕ} (S : Fin n → Even C.super) (e : X ≅ ⨁ S) :
    (toOldData C).HasDecomposition X (fun i => (S i : C.data.Obj)) := by
  let F := evenToTotal C.super
  let i (j : Fin n) := biproduct.ι S j ≫ e.inv
  let r (j : Fin n) := e.hom ≫ biproduct.π S j
  refine ⟨fun j => F.map (i j), fun j => F.map (r j),
    fun j => evenPoint_mem_grade C.super (i j),
    fun j => evenPoint_mem_grade C.super (r j), ?_, ?_, ?_⟩
  · intro j
    have h : i j ≫ r j = 𝟙 _ := by simp [i, r, Category.assoc]
    exact (F.map_comp (i j) (r j)).symm.trans ((congrArg F.map h).trans (F.map_id _))
  · intro j k hjk
    have h : i j ≫ r k = 0 := by simp [i, r, Category.assoc, hjk]
    exact (F.map_comp (i j) (r k)).symm.trans ((congrArg F.map h).trans (F.map_zero _ _))
  · have ht : ∑ j, r j ≫ i j = 𝟙 X := by
      calc
        _ = e.hom ≫ (∑ j, biproduct.π S j ≫ biproduct.ι S j) ≫ e.inv := by
          simp only [i, r, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = _ := by rw [biproduct.total, Category.id_comp, Iso.hom_inv_id]
    rw [legacy_finSum C]
    change (∑ j, F.map (r j) ≫ F.map (i j)) = F.map (𝟙 X)
    simp only [← F.map_comp, ← F.map_sum, ht]

theorem legacyFiniteBiproducts [HasFiniteBiproducts (Even C.super)]
    {n : ℕ} (S : Fin n → (toOldData C).Obj) : (toOldData C).HasFiniteBiproduct S := by
  let S' : Fin n → Even C.super := fun i => evenObj C.super (S i)
  exact ⟨biproduct (C := Even C.super) S', legacyDecomposition C _ S' (Iso.refl _)⟩

theorem legacySemisimple (A : FusionPiSupercategory)
    (X : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj) :
    ∃ (n : ℕ) (S : Fin n → (toOldData A.toMonoidalPiSupercategory.monoidal).Obj),
      (∀ i, (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple (S i)) ∧
        (toOldData A.toMonoidalPiSupercategory.monoidal).HasDecomposition X S := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := A.semisimple (evenObj _ X)
  exact ⟨n, fun i => S i,
    fun i => (legacySimple_iff A.toMonoidalPiSupercategory.monoidal (S i)).mpr (hS i),
    legacyDecomposition A.toMonoidalPiSupercategory.monoidal _ S e⟩

theorem legacyFiniteBasis (A : FusionPiSupercategory)
    (X Y : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj) :
    (toOldData A.toMonoidalPiSupercategory.monoidal).HasFiniteBasis X Y := by
  letI (a : ZMod 2) : FiniteDimensional ℝ (A.data.Hom X Y a) := A.hom_finite X Y a
  let b := Module.finBasis ℝ (THom A.data.toSupercategoryData X Y)
  refine ⟨_, b, fun f i => b.repr f i, ?_, ?_⟩
  · intro f
    rw [legacy_finSum]
    exact b.sum_repr f
  · intro f c hc
    rw [legacy_finSum] at hc
    rw [← hc]
    exact (b.repr_sum_self c).symm

end RMod.Legacy.Hierarchy
