import RMod.Hierarchy.Bridge.Fusion

/-!
# Super-multiplicities as even biproducts

An odd summand is converted into an even inclusion from the parity shift
of the unit. Its projection uses the inverse odd comparison. The old
matrix identities then give the required even biproduct isomorphism.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace RMod.Legacy.Hierarchy
variable (C : WeaklyPointedSuperfusion.{0, 0}) (p : Classification.Pi C.data)

theorem oldSuperMultiplicity_evenIso (A : C.data.Obj) (n m : ℕ)
    (h : C.data.HasSuperMultiplicity A C.data.tensorUnit n m) :
    Nonempty (oldEvenObj C A ≅ ⨁ (fun j : Fin n ⊕ Fin m =>
      oldEvenObj C (Sum.elim (fun _ => C.data.tensorUnit)
        (fun _ => p.data.shiftObj C.data.tensorUnit) j))) := by
  classical
  obtain ⟨i, r, hi, hr, hd, ho, ht⟩ := h
  let S : Fin n ⊕ Fin m → Classification.LinearCategory C :=
    Sum.elim (fun _ => C.data.tensorUnit) (fun _ => p.data.shiftObj C.data.tensorUnit)
  let e : ∀ j, S j ≅ (C.data.tensorUnit : Classification.LinearCategory C) :=
    fun j => match j with
    | .inl _ => Iso.refl _
    | .inr _ => ⟨p.data.zHom C.data.tensorUnit, p.data.zInv C.data.tensorUnit,
        (p.laws.z_iso C.laws _).hom_inv, (p.laws.z_iso C.laws _).inv_hom⟩
  have he (j : Fin n ⊕ Fin m) :
      C.data.IsHomogeneous (WeaklyPointedSuperfusionData.superIndexParity j) (e j).hom ∧
      C.data.IsHomogeneous (WeaklyPointedSuperfusionData.superIndexParity j) (e j).inv := by
    cases j with
    | inl j => exact ⟨C.laws.id_even _, C.laws.id_even _⟩
    | inr j => exact ⟨p.laws.z_hom_odd C.laws _, p.laws.z_inv_odd C.laws _⟩
  let U : Classification.LinearCategory C := C.data.tensorUnit
  let V : Classification.LinearCategory C := A
  let incl (j : Fin n ⊕ Fin m) : U ⟶ V := i j
  let proj (j : Fin n ⊕ Fin m) : V ⟶ U := r j
  have hd' (j : Fin n ⊕ Fin m) :
      incl j ≫ proj j = 𝟙 U := hd j
  have ho' (j k : Fin n ⊕ Fin m) (hjk : j ≠ k) :
      incl j ≫ proj k = 0 := ho j k hjk
  let b : Bicone (fun j => oldEvenObj C (S j)) := {
    pt := oldEvenObj C A
    ι j := ⟨(e j).hom ≫ incl j, by
      have hg := C.laws.comp_grade _ _ (he j).1 (hi j)
      simp only [CharTwo.add_self_eq_zero] at hg
      exact hg⟩
    π j := ⟨proj j ≫ (e j).inv, by
      have hg := C.laws.comp_grade _ _ (hr j) (he j).2
      simp only [CharTwo.add_self_eq_zero] at hg
      exact hg⟩
    ι_π j k := by
      by_cases hjk : j = k
      · subst k
        simp only [dite_true, eqToHom_refl]
        apply WideSubcategory.hom_ext
        change ((e j).hom ≫ incl j) ≫ (proj j ≫ (e j).inv) = 𝟙 _
        rw [Category.assoc, ← Category.assoc (incl j), hd', Category.id_comp, Iso.hom_inv_id]
      · rw [dif_neg hjk]
        apply WideSubcategory.hom_ext
        change ((e j).hom ≫ incl j) ≫ (proj k ≫ (e k).inv) = 0
        rw [Category.assoc, ← Category.assoc (incl j), ho' j k hjk,
          zero_comp, comp_zero] }
  have hb : b.IsBilimit := by
    apply isBilimitOfTotal
    apply WideSubcategory.hom_ext
    let F := wideSubcategoryInclusion (Superfusion.Category.evenMorphismProperty ℝ
      (Classification.LinearCategory C))
    have hs := F.map_sum (fun j => b.π j ≫ b.ι j) Finset.univ
    change F.map (∑ j, b.π j ≫ b.ι j) = _
    rw [hs]
    change (∑ j, (proj j ≫ (e j).inv) ≫ ((e j).hom ≫ incl j) : V ⟶ V) = 𝟙 V
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [Fintype.sum_sum_type]
    dsimp only [WeaklyPointedSuperfusionData.superFinSum] at ht
    simp only [Classification.LinearCategory.finSum_eq_sum C] at ht
    exact ht
  exact ⟨biproduct.uniqueUpToIso _ hb⟩

theorem ofOldWeaklyInvertible (P : Classification.PiSuperfusion.{0, 0})
    (X : Even (ofOldSupercategory P.toWeaklyPointedSuperfusion)) (hX : Simple X) :
    IsWeaklyInvertible (ofOldFusionPiSupercategory P).toMonoidalPiSupercategory X := by
  let C := P.toWeaklyPointedSuperfusion
  let p : Classification.Pi C.data := ⟨P.data.pi, P.laws.pi⟩
  obtain ⟨Y, hY, n, m, _, hm⟩ := P.laws.weakly_pointed X ((oldSimple_iff C X).mpr hX)
  refine ⟨evenObj (ofOldSupercategory C) Y, ⟨ofOldExactPairing C X Y hY⟩, n, m, ?_⟩
  let S : Fin n ⊕ Fin m → Even (ofOldSupercategory C) :=
    Sum.elim (fun _ => evenObj (ofOldSupercategory C) C.data.tensorUnit)
      (fun _ => evenObj (ofOldSupercategory C) (p.data.shiftObj C.data.tensorUnit))
  obtain ⟨e⟩ := oldSuperMultiplicity_evenIso C p (C.data.tensorObj X Y) n m hm
  change Nonempty (evenObj (ofOldSupercategory C) (C.data.tensorObj X Y) ≅ ⨁ S)
  let eS : ∀ j : Fin n ⊕ Fin m,
      oldEvenObj C (Sum.elim (fun _ => C.data.tensorUnit)
        (fun _ => p.data.shiftObj C.data.tensorUnit) j) ≅ (evenForget C).obj (S j) := by
    intro j
    cases j <;> exact Iso.refl _
  exact ⟨(evenForget C).preimageIso
    (e ≪≫ biproduct.mapIso eS ≪≫ ((evenForget C).mapBiproduct S).symm)⟩

def ofOldWeaklyPointedFusionPiSupercategory (P : Classification.PiSuperfusion.{0, 0}) :
    WeaklyPointedFusionPiSupercategory where
  toFusionPiSupercategory := ofOldFusionPiSupercategory P
  splitUnit := ofOldFusionSplitUnit P
  weaklyPointed := ofOldWeaklyInvertible P

end RMod.Legacy.Hierarchy
