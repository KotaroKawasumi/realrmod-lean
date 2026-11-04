import RMod.Classification.Instances.SpanFamilySumData
import RMod.Classification.Proofs.EvenBiproductFullBicone

/-!
# The component matrix defines an ordinary functor on all morphisms

Each inclusion followed by the diagonal matrix is its component map
followed by the target inclusion. The full-Hom universal property of the
chosen even biproduct then proves identity and composition preservation.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)

theorem spanFamilySum_inclusion_map {X Y : SpanFamilyCategory C S} (f : X ⟶ Y) (i : I) :
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i ≫ (spanFamilySumData C S).map f =
      (f i).hom ≫ (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).ι i := by
  classical
  let bX := evenBiproductFullBicone C (spanFamilyEvenObjects C S X)
  let bY := evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)
  change bX.ι i ≫ (∑ j, (bX.π j ≫ (f j).hom) ≫ bY.ι j) = (f i).hom ≫ bY.ι i
  simp only [Category.assoc]
  rw [comp_sum, Finset.sum_eq_single i]
  · rw [← Category.assoc, bicone_ι_π_self, Category.id_comp]
    rfl
  · intro j _ hji
    rw [← Category.assoc, bicone_ι_π_ne bX hji.symm, Limits.zero_comp]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem spanFamilySum_map_id (X : SpanFamilyCategory C S) :
    (spanFamilySumData C S).map (𝟙 X) = 𝟙 (spanFamilySumObj C S X) := by
  apply (evenBiproductFullIsBilimit C (spanFamilyEvenObjects C S X)).isColimit.hom_ext
  rintro ⟨i⟩
  change (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i ≫
    (spanFamilySumData C S).map (𝟙 X) =
      (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i ≫ 𝟙 _
  rw [spanFamilySum_inclusion_map, Category.comp_id]
  exact Category.id_comp _

theorem spanFamilySum_map_comp {X Y Z : SpanFamilyCategory C S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spanFamilySumData C S).map (f ≫ g) = (spanFamilySumData C S).map f ≫ (spanFamilySumData C S).map g := by
  apply (evenBiproductFullIsBilimit C (spanFamilyEvenObjects C S X)).isColimit.hom_ext
  rintro ⟨i⟩
  let ix : C.data.Hom (X i).obj (spanFamilySumObj C S X) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i
  let iy : C.data.Hom (Y i).obj (spanFamilySumObj C S Y) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).ι i
  let iz : C.data.Hom (Z i).obj (spanFamilySumObj C S Z) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Z)).ι i
  let fi : C.data.Hom (X i).obj (Y i).obj := (f i).hom
  let gi : C.data.Hom (Y i).obj (Z i).obj := (g i).hom
  let mf : C.data.Hom (spanFamilySumObj C S X) (spanFamilySumObj C S Y) := (spanFamilySumData C S).map f
  let mg : C.data.Hom (spanFamilySumObj C S Y) (spanFamilySumObj C S Z) := (spanFamilySumData C S).map g
  let mfg : C.data.Hom (spanFamilySumObj C S X) (spanFamilySumObj C S Z) := (spanFamilySumData C S).map (f ≫ g)
  have hf : C.data.comp ix mf = C.data.comp fi iy := spanFamilySum_inclusion_map C S f i
  have hg : C.data.comp iy mg = C.data.comp gi iz := spanFamilySum_inclusion_map C S g i
  have hfg : C.data.comp ix mfg = C.data.comp (C.data.comp fi gi) iz :=
    spanFamilySum_inclusion_map C S (f ≫ g) i
  change C.data.comp ix mfg = C.data.comp ix (C.data.comp mf mg)
  calc
    _ = C.data.comp (C.data.comp fi gi) iz := hfg
    _ = C.data.comp fi (C.data.comp gi iz) := C.laws.comp_assoc _ _ _
    _ = C.data.comp fi (C.data.comp iy mg) := congrArg (C.data.comp fi) hg.symm
    _ = C.data.comp (C.data.comp fi iy) mg := (C.laws.comp_assoc _ _ _).symm
    _ = C.data.comp (C.data.comp ix mf) mg := congrArg (fun q => C.data.comp q mg) hf.symm
    _ = _ := C.laws.comp_assoc _ _ _

end RMod.Classification
