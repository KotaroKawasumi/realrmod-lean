import RMod.BrundanEllis.StackingPairing
import RMod.BrundanEllis.StackingOrbitTensor

/-! The two variables of a super exterior pairing give additive enriched
functors. This allows completion arguments to use the actual pairing, without
assuming that it preserves parity shifts by a chosen even comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
section
universe u v w
variable (V : Type v) [Category.{w} V] [MonoidalCategory V] [BraidedCategory V]
  {C D : Type u} [EnrichedCategory V C] [EnrichedCategory V D]
omit [BraidedCategory V] in
private theorem eId_mul (X : C) :
    (eId V X ⊗ₘ eId V X) ≫ eComp V X X X = (λ_ (𝟙_ V)).hom ≫ eId V X := by
  apply (cancel_epi (λ_ (𝟙_ V)).inv).1
  rw [Iso.inv_hom_id_assoc]
  have h := ForgetEnrichment.homTo_comp V
    (𝟙 (ForgetEnrichment.of V X)) (𝟙 (ForgetEnrichment.of V X))
  simpa only [Category.id_comp, ForgetEnrichment.homTo_id, ForgetEnrichment.to_of, Category.assoc] using h.symm

/-- Insert a fixed object and its enriched identity on the left. -/
def insertLeft (I : C) : EnrichedFunctor V D (EnrichedTensorProduct V C D) where
  obj X := EnrichedTensorProduct.of V I X
  map X Y := (λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 (X ⟶[V] Y))
  map_id X := by
    change eId V X ≫ (λ_ (X ⟶[V] X)).inv ≫ (eId V I ⊗ₘ 𝟙 _) =
      (λ_ (𝟙_ V)).inv ≫ (eId V I ⊗ₘ eId V X)
    rw [leftUnitor_inv_naturality_assoc, tensorHom_id, MonoidalCategory.tensorHom_def']
  map_comp X Y Z := by
    change eComp V X Y Z ≫ (λ_ (X ⟶[V] Z)).inv ≫ (eId V I ⊗ₘ 𝟙 _) =
      (((λ_ (X ⟶[V] Y)).inv ≫ (eId V I ⊗ₘ 𝟙 _)) ⊗ₘ
        ((λ_ (Y ⟶[V] Z)).inv ≫ (eId V I ⊗ₘ 𝟙 _))) ≫ tensorμ _ _ _ _ ≫
          (eComp V I I I ⊗ₘ eComp V X Y Z)
    rw [← tensorHom_comp_tensorHom, Category.assoc, tensorμ_natural_assoc,
      tensorHom_comp_tensorHom, eId_mul]
    have h := congrArg (fun k =>
      ((λ_ (X ⟶[V] Y)).inv ⊗ₘ (λ_ (Y ⟶[V] Z)).inv) ≫ k)
      (leftUnitor_monoidal (X ⟶[V] Y) (Y ⟶[V] Z))
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id] at h
    have q := congrArg (fun k => k ≫ (λ_ ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z))).inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] at q
    simp only [MonoidalCategory.tensorHom_def,
      comp_whiskerRight, Category.assoc]
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, q]
    simp [MonoidalCategory.tensorHom_def, Category.assoc]


/-- Insert a fixed object and its enriched identity on the right. -/
def insertRight (I : D) : EnrichedFunctor V C (EnrichedTensorProduct V C D) where
  obj X := EnrichedTensorProduct.of V X I
  map X Y := (ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 (X ⟶[V] Y) ⊗ₘ eId V I)
  map_id X := by
    change eId V X ≫ (ρ_ (X ⟶[V] X)).inv ≫ (𝟙 _ ⊗ₘ eId V I) =
      (λ_ (𝟙_ V)).inv ≫ (eId V X ⊗ₘ eId V I)
    rw [rightUnitor_inv_naturality_assoc, id_tensorHom, MonoidalCategory.tensorHom_def, unitors_inv_equal]
  map_comp X Y Z := by
    change eComp V X Y Z ≫ (ρ_ (X ⟶[V] Z)).inv ≫ (𝟙 _ ⊗ₘ eId V I) =
      (((ρ_ (X ⟶[V] Y)).inv ≫ (𝟙 _ ⊗ₘ eId V I)) ⊗ₘ
        ((ρ_ (Y ⟶[V] Z)).inv ≫ (𝟙 _ ⊗ₘ eId V I))) ≫ tensorμ _ _ _ _ ≫
          (eComp V X Y Z ⊗ₘ eComp V I I I)
    rw [← tensorHom_comp_tensorHom, Category.assoc, tensorμ_natural_assoc,
      tensorHom_comp_tensorHom, eId_mul]
    have h := congrArg (fun k =>
      ((ρ_ (X ⟶[V] Y)).inv ⊗ₘ (ρ_ (Y ⟶[V] Z)).inv) ≫ k)
      (rightUnitor_monoidal (X ⟶[V] Y) (Y ⟶[V] Z))
    simp only [tensorHom_comp_tensorHom, Iso.inv_hom_id, id_tensorHom_id] at h
    have q := congrArg (fun k => k ≫ (ρ_ ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z))).inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] at q
    simp only [MonoidalCategory.tensorHom_def',
      whiskerLeft_comp, Category.assoc]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, q]
    simp [MonoidalCategory.tensorHom_def', Category.assoc]

end
variable {A B D : WeaklyPointedFusionPiSuperCat}

def pairLeft (F : SuperFunctor (SuperTensorProduct A B) D) (X : A) :
    SuperFunctor B D := (insertLeft SuperVec X).comp SuperVec F

def pairRight (F : SuperFunctor (SuperTensorProduct A B) D) (Y : B) :
    SuperFunctor A D := (insertRight SuperVec Y).comp SuperVec F

/-- Enrichment over real super vector spaces implies additivity on even maps. -/
instance forgetAdditive (F : SuperFunctor A B) : F.forget.Additive where
  map_add {X Y} f g := by
    apply funext
    intro a
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => map_add (F.map X Y a).hom (f a x) (g a x))

end Stacking
namespace AddPiHull
variable {A B : WeaklyPointedFusionPiSuperCat} {I J : Type}
  {Z : I → Even A} {W : J → Even B}

/-- For an enriched functor, it suffices to check the original generators. -/
theorem map_super (F : SuperFunctor A B)
    (h : ∀ i, AddPiHull B W (F.forget.obj (Z i)))
    {X : Even A} (hX : AddPiHull A Z X) : AddPiHull B W (F.forget.obj X) := by
  apply map F.forget (fun i p => ?_) hX
  cases p
  · exact h i
  · exact of_orbit (Stacking.orbit_symm
      (Stacking.map_orbit F (Stacking.parity_orbit (Z i)))) (h i)

end AddPiHull
end RMod.BrundanEllis
