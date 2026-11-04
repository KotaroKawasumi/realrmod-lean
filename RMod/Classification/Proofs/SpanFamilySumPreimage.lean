import RMod.Classification.Instances.SpanFamilySumPreimage
import RMod.Classification.Proofs.HomogeneousSpanOrthogonality

/-!
# Matrix inversion for sums of distinct simple-orbit components

Taking diagonal entries recovers each input map. Conversely, every
between-component entry of an arbitrary map vanishes by orthogonality.
The two full-Hom universal properties then recover the whole map from
its diagonal entries. Both inverse identities concern the specified map.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} [Fintype I] (S : I → C.data.Obj)

theorem spanFamilySum_preimage_map {X Y : SpanFamilyCategory C S} (f : X ⟶ Y) :
    spanFamilySumPreimage C S ((spanFamilySum C S).map f) = f := by
  funext i
  apply ObjectProperty.hom_ext
  let ix : C.data.Hom (X i).obj (spanFamilySumObj C S X) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i
  let iy : C.data.Hom (Y i).obj (spanFamilySumObj C S Y) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).ι i
  let py : C.data.Hom (spanFamilySumObj C S Y) (Y i).obj :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).π i
  let fi : C.data.Hom (X i).obj (Y i).obj := (f i).hom
  let mf : C.data.Hom (spanFamilySumObj C S X) (spanFamilySumObj C S Y) := (spanFamilySum C S).map f
  have hf : C.data.comp ix mf = C.data.comp fi iy := spanFamilySum_inclusion_map C S f i
  have hi : C.data.comp iy py = C.data.id (Y i).obj :=
    bicone_ι_π_self (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)) i
  change C.data.comp (C.data.comp ix mf) py = fi
  rw [hf, C.laws.comp_assoc, hi, C.laws.comp_id]

theorem spanFamilySum_map_preimage
    (hS : ∀ i, C.data.IsSimple (S i))
    (hST : ∀ i j, i ≠ j → ¬ SameParityOrbit C.data (S i) (S j))
    {X Y : SpanFamilyCategory C S} (f : (spanFamilySum C S).obj X ⟶ (spanFamilySum C S).obj Y) :
    (spanFamilySum C S).map (spanFamilySumPreimage C S f) = f := by
  apply (evenBiproductFullIsBilimit C (spanFamilyEvenObjects C S X)).isColimit.hom_ext
  rintro ⟨i⟩
  apply (evenBiproductFullIsBilimit C (spanFamilyEvenObjects C S Y)).isLimit.hom_ext
  rintro ⟨j⟩
  let ix : C.data.Hom (X i).obj (spanFamilySumObj C S X) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S X)).ι i
  let iy : C.data.Hom (Y i).obj (spanFamilySumObj C S Y) :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).ι i
  let pi : C.data.Hom (spanFamilySumObj C S Y) (Y i).obj :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).π i
  let pj : C.data.Hom (spanFamilySumObj C S Y) (Y j).obj :=
    (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)).π j
  let fi := C.data.comp (C.data.comp ix f) pi
  let mf : C.data.Hom (spanFamilySumObj C S X) (spanFamilySumObj C S Y) :=
    (spanFamilySum C S).map (spanFamilySumPreimage C S f)
  have hm : C.data.comp ix mf = C.data.comp fi iy :=
    spanFamilySum_inclusion_map C S (spanFamilySumPreimage C S f) i
  change C.data.comp (C.data.comp ix mf) pj = C.data.comp (C.data.comp ix f) pj
  rw [hm, C.laws.comp_assoc]
  by_cases hij : i = j
  · subst j
    have hi : C.data.comp iy pi = C.data.id (Y i).obj :=
      bicone_ι_π_self (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)) i
    change C.data.comp fi (C.data.comp iy pi) = fi
    rw [hi, C.laws.comp_id]
  · have hij' : C.data.comp iy pj = C.data.zero :=
      bicone_ι_π_ne (evenBiproductFullBicone C (spanFamilyEvenObjects C S Y)) hij
    rw [hij', raw_comp_zero C.laws]
    exact (hom_zero_of_distinct_spans C (hS i) (hS j) (hST i j hij) (X i).property (Y j).property _).symm

end RMod.Classification
