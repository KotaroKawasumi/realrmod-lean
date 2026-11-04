import RMod.Classification.Instances.SpanNaturalExtensionData
import RMod.Classification.Proofs.SpanNaturalExt
import RMod.Classification.Proofs.SpanHomSums
import RMod.Classification.Proofs.ParityPowers

/-!
# Extending a signed generator intertwiner

The matrix extension has the stated degree. Its defining intertwining
equation determines its composite with every homogeneous map from the
generator. The source total matrix identity gives this equation without
any choice of a homogeneous basis in individual Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Preadditive

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2} (t : SpanIntertwiner F G a)

theorem spanNaturalExtension_grade (X : HomogeneousSpanCategory C S) :
    D.data.IsHomogeneous a ((spanNaturalExtensionData F.data G.data a t.data).app X).hom := by
  apply span_sum_grade
  intro i
  apply D.laws.grade_smul
  have hp := F.laws.map_grade
    (ObjectProperty.homMk ((spanPresentation X).data.projection i) : X ⟶ spanGenerator C S)
    ((spanPresentation X).laws.projection_grade i)
  have hi := G.laws.map_grade
    (ObjectProperty.homMk ((spanPresentation X).data.inclusion i) : spanGenerator C S ⟶ X)
    ((spanPresentation X).laws.inclusion_grade i)
  have hg := D.laws.comp_grade _ _ hp (D.laws.comp_grade _ _ t.laws.grade hi)
  have he : (spanPresentation X).data.parity i + (a + (spanPresentation X).data.parity i) = a := by
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  rw [he] at hg
  exact hg

theorem spanNaturalExtension_on_generator_hom {X : HomogeneousSpanCategory C S} {b : ZMod 2}
    (k : spanGenerator C S ⟶ X) (hk : C.data.IsHomogeneous b k.hom) :
    F.toFunctor.map k ≫ (spanNaturalExtensionData F.data G.data a t.data).app X =
      ((-1 : ℝ) ^ (a * b).val) • (t.data.hom ≫ G.toFunctor.map k) := by
  let p : Fin (spanSize X) → (X ⟶ spanGenerator C S) :=
    fun j => ObjectProperty.homMk ((spanPresentation X).data.projection j)
  let i : Fin (spanSize X) → (spanGenerator C S ⟶ X) :=
    fun j => ObjectProperty.homMk ((spanPresentation X).data.inclusion j)
  let q := (spanPresentation X).data.parity
  let u : F.toFunctor.obj (spanGenerator C S) ⟶ G.toFunctor.obj (spanGenerator C S) := t.data.hom
  have htotal : ∑ j, (k ≫ p j) ≫ i j = k := by
    simp only [Category.assoc, ← comp_sum]
    have ht : ∑ j, p j ≫ i j = 𝟙 X := spanPresentation_total X
    rw [ht, Category.comp_id]
  change F.toFunctor.map k ≫
    (∑ j, ((-1 : ℝ) ^ (a * q j).val) • (F.toFunctor.map (p j) ≫ u ≫ G.toFunctor.map (i j))) =
      ((-1 : ℝ) ^ (a * b).val) • (u ≫ G.toFunctor.map k)
  calc
    _ = ∑ j, ((-1 : ℝ) ^ (a * q j).val) •
        ((F.toFunctor.map (k ≫ p j) ≫ u) ≫ G.toFunctor.map (i j)) := by
      simp only [comp_sum, Linear.comp_smul, F.toFunctor.map_comp, Category.assoc]
    _ = ∑ j, ((-1 : ℝ) ^ (a * b).val) • (u ≫ G.toFunctor.map ((k ≫ p j) ≫ i j)) := by
      apply Finset.sum_congr rfl
      intro j _
      have hkp : C.data.IsHomogeneous (b + q j) (k ≫ p j).hom :=
        C.laws.comp_grade _ _ hk ((spanPresentation X).laws.projection_grade j)
      have hu : F.toFunctor.map (k ≫ p j) ≫ u =
          ((-1 : ℝ) ^ (a * (b + q j)).val) • (u ≫ G.toFunctor.map (k ≫ p j)) :=
        t.laws.intertwines (k ≫ p j) hkp
      rw [hu, Linear.smul_comp, smul_smul, koszul_power_cancel]
      simp only [G.toFunctor.map_comp, Category.assoc]
    _ = _ := by rw [← Finset.smul_sum, ← comp_sum, ← G.toFunctor.map_sum, htotal]

theorem spanNaturalExtension_naturality {X Y : HomogeneousSpanCategory C S} {b : ZMod 2}
    (f : X ⟶ Y) (hf : C.data.IsHomogeneous b f.hom) :
    F.toFunctor.map f ≫ (spanNaturalExtensionData F.data G.data a t.data).app Y =
      ((-1 : ℝ) ^ (a * b).val) •
        ((spanNaturalExtensionData F.data G.data a t.data).app X ≫ G.toFunctor.map f) := by
  apply F.hom_ext_generator
  intro j
  let k : spanGenerator C S ⟶ X := ObjectProperty.homMk ((spanPresentation X).data.inclusion j)
  let q := (spanPresentation X).data.parity j
  let u : F.toFunctor.obj (spanGenerator C S) ⟶ G.toFunctor.obj (spanGenerator C S) := t.data.hom
  let ex : F.toFunctor.obj X ⟶ G.toFunctor.obj X :=
    (spanNaturalExtensionData F.data G.data a t.data).app X
  let ey : F.toFunctor.obj Y ⟶ G.toFunctor.obj Y :=
    (spanNaturalExtensionData F.data G.data a t.data).app Y
  have hk : C.data.IsHomogeneous q k.hom := (spanPresentation X).laws.inclusion_grade j
  have hkf : C.data.IsHomogeneous (q + b) (k ≫ f).hom := C.laws.comp_grade _ _ hk hf
  have hleft : F.toFunctor.map (k ≫ f) ≫ ey =
      ((-1 : ℝ) ^ (a * (q + b)).val) • (u ≫ G.toFunctor.map (k ≫ f)) :=
    spanNaturalExtension_on_generator_hom t (k ≫ f) hkf
  have hright : F.toFunctor.map k ≫ ex = ((-1 : ℝ) ^ (a * q).val) • (u ≫ G.toFunctor.map k) :=
    spanNaturalExtension_on_generator_hom t k hk
  change F.toFunctor.map k ≫ (F.toFunctor.map f ≫ ey) =
    F.toFunctor.map k ≫ (((-1 : ℝ) ^ (a * b).val) • (ex ≫ G.toFunctor.map f))
  calc
    _ = F.toFunctor.map (k ≫ f) ≫ ey := by rw [F.toFunctor.map_comp, Category.assoc]
    _ = ((-1 : ℝ) ^ (a * (q + b)).val) • (u ≫ G.toFunctor.map (k ≫ f)) := hleft
    _ = ((-1 : ℝ) ^ (a * b).val) • ((F.toFunctor.map k ≫ ex) ≫ G.toFunctor.map f) := by
      rw [hright, Linear.smul_comp, smul_smul, G.toFunctor.map_comp, Category.assoc,
        koszul_power_add_right]
      rw [mul_comm ((-1 : ℝ) ^ (a * q).val) ((-1 : ℝ) ^ (a * b).val)]
    _ = _ := by rw [Linear.comp_smul, Category.assoc]

theorem spanNaturalExtensionLaws :
    SpanHomogeneousNatLaws a (spanNaturalExtensionData F.data G.data a t.data) where
  grade := spanNaturalExtension_grade t
  naturality f hf := spanNaturalExtension_naturality t f hf

end RMod.Classification
