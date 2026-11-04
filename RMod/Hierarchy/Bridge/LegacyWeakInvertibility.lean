import RMod.Hierarchy.Bridge.LegacyParity
import RMod.Hierarchy.Bridge.LegacyFinite
import RMod.Hierarchy.Instances.NonzeroPairing

/-!
# Weak invertibility in the legacy presentation

An even copy of the parity-shifted unit becomes an odd copy of the unit
by composition with the specified parity isomorphism. A simple object
cannot have zero tensor product with an exact dual, so the resulting
super-multiplicity is nonempty.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace RMod.Legacy.Hierarchy

theorem legacySuperMultiplicity (A : MonoidalPiSupercategory)
    [HasFiniteBiproducts (Even A.monoidal.super)] (X : Even A.monoidal.super) (n m : ℕ)
    (e : X ≅ ⨁ (fun j : Fin n ⊕ Fin m =>
      Sum.elim (fun _ => (𝟙_ (Even A.monoidal.super)))
        (fun _ => evenObj A.monoidal.super (A.data.parityShift.functor.obj A.data.monoidal.unit)) j)) :
    (toOldData A.monoidal).HasSuperMultiplicity X A.data.monoidal.unit n m := by
  classical
  let C := A.monoidal
  let F := evenToTotal C.super
  let U : TotalCategory C.super := totalObj C.super A.data.monoidal.unit
  let S : Fin n ⊕ Fin m → Even C.super :=
    Sum.elim (fun _ => (𝟙_ (Even C.super)))
      (fun _ => evenObj C.super (A.data.parityShift.functor.obj A.data.monoidal.unit))
  let d : ∀ j, U ≅ F.obj (S j) := fun j => match j with
    | .inl _ => Iso.refl _
    | .inr _ => legacyParityIso A
  have hd (j : Fin n ⊕ Fin m) :
      (d j).hom ∈ grade C.super U (F.obj (S j)) (WeaklyPointedSuperfusionData.superIndexParity j) ∧
      (d j).inv ∈ grade C.super (F.obj (S j)) U (WeaklyPointedSuperfusionData.superIndexParity j) := by
    cases j with
    | inl j => exact ⟨evenPoint_mem_grade C.super (C.data.id U), evenPoint_mem_grade C.super (C.data.id U)⟩
    | inr j => exact ⟨(toOldParityLaws A).inv_odd, (toOldParityLaws A).hom_odd⟩
  let i (j : Fin n ⊕ Fin m) : S j ⟶ X := biproduct.ι S j ≫ e.inv
  let r (j : Fin n ⊕ Fin m) : X ⟶ S j := e.hom ≫ biproduct.π S j
  have hdiag (j : Fin n ⊕ Fin m) : i j ≫ r j = 𝟙 _ := by simp [i, r, Category.assoc]
  have hoff (j k : Fin n ⊕ Fin m) (hjk : j ≠ k) : i j ≫ r k = 0 := by
    simp [i, r, Category.assoc, hjk]
  have ht : ∑ j, r j ≫ i j = 𝟙 X := by
    calc
      _ = e.hom ≫ (∑ j, biproduct.π S j ≫ biproduct.ι S j) ≫ e.inv := by
        simp only [i, r, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = _ := by rw [biproduct.total, Category.id_comp, Iso.hom_inv_id]
  refine ⟨fun j => (d j).hom ≫ F.map (i j), fun j => F.map (r j) ≫ (d j).inv, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have h := tComp_mem_grade C.super _ _ (hd j).1 (evenPoint_mem_grade C.super (i j))
    simp only [add_zero] at h
    exact h
  · intro j
    have h := tComp_mem_grade C.super _ _ (evenPoint_mem_grade C.super (r j)) (hd j).2
    simp only [zero_add] at h
    exact h
  · intro j
    change ((d j).hom ≫ F.map (i j)) ≫ (F.map (r j) ≫ (d j).inv) = 𝟙 U
    rw [Category.assoc, ← Category.assoc (F.map (i j)), ← F.map_comp, hdiag,
      F.map_id, Category.id_comp, Iso.hom_inv_id]
  · intro j k hjk
    change ((d j).hom ≫ F.map (i j)) ≫ (F.map (r k) ≫ (d k).inv) = 0
    rw [Category.assoc, ← Category.assoc (F.map (i j)), ← F.map_comp, hoff j k hjk,
      F.map_zero, zero_comp, comp_zero]
  · change (toOldData C).add ((toOldData C).finSum n (fun j => (F.map (r (.inl j)) ≫ (d (.inl j)).inv) ≫
        ((d (.inl j)).hom ≫ F.map (i (.inl j)))))
      ((toOldData C).finSum m (fun j => (F.map (r (.inr j)) ≫ (d (.inr j)).inv) ≫
        ((d (.inr j)).hom ≫ F.map (i (.inr j))))) = 𝟙 (F.obj X)
    rw [legacy_finSum C, legacy_finSum C]
    change (∑ j, (F.map (r (.inl j)) ≫ (d (.inl j)).inv) ≫
        ((d (.inl j)).hom ≫ F.map (i (.inl j)))) +
      (∑ j, (F.map (r (.inr j)) ≫ (d (.inr j)).inv) ≫
        ((d (.inr j)).hom ≫ F.map (i (.inr j)))) = 𝟙 (F.obj X)
    have hs : (∑ j, (F.map (r j) ≫ (d j).inv) ≫ ((d j).hom ≫ F.map (i j))) = 𝟙 (F.obj X) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp, ← F.map_sum, ht, F.map_id]
    rw [Fintype.sum_sum_type] at hs
    exact hs

theorem legacyWeaklyInvertible (A : WeaklyPointedFusionPiSupercategory)
    (X : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj)
    (hX : (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple X) :
    (toOldData A.toMonoidalPiSupercategory.monoidal).IsWeaklyInvertible X := by
  let X' := evenObj A.toMonoidalPiSupercategory.monoidal.super X
  haveI : Simple X' := (legacySimple_iff _ X').mp hX
  obtain ⟨Y, ⟨hY⟩, n, m, ⟨e⟩⟩ := A.weaklyPointed X' inferInstance
  letI : ExactPairing X' Y := hY
  have hn : 0 < n + m := by
    obtain ⟨j⟩ := simple_pairing_nonempty_biproduct X' Y _ e
    cases j with
    | inl j => have hj := j.isLt; omega
    | inr j => have hj := j.isLt; omega
  exact ⟨Y, legacyExactPairing A.toMonoidalPiSupercategory.monoidal X' Y, n, m, hn,
    legacySuperMultiplicity A.toMonoidalPiSupercategory (X' ⊗ Y) n m e⟩

end RMod.Legacy.Hierarchy
