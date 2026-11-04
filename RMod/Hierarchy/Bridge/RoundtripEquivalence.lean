import RMod.Hierarchy.Bridge.RoundtripTensor
import RMod.Hierarchy.Bridge.OldEvenValues

/-!
# The new-old-new comparison as a monoidal superequivalence

Objects and even coherence maps are retained. Homogeneous inclusion and
evaluation supply inverse enriched functors with identity comparisons.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable (A : WeaklyPointedFusionPiSupercategory)

def roundtripEquivalenceData : MonoidalSuperequivalenceData
    A.toMonoidalPiSupercategory.monoidal (ofOldMonoidalSupercategory (legacyCategory A)) where
  forward := roundtripForwardData A
  backward := roundtripBackwardData A
  tensorIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  unit _ := Iso.refl _
  counit _ := Iso.refl _

theorem roundtripEquivalenceLaws : MonoidalSuperequivalenceLaws (roundtripEquivalenceData A) where
  forward := roundtripForwardLaws A
  backward := roundtripBackwardLaws A
  unit_natural f := by
    change tComp (originalSuper A).data f (evenPoint ((originalSuper A).data.id _)) =
      tComp (originalSuper A).data (evenPoint ((originalSuper A).data.id _))
        (tMap (roundtripBackwardData A) (tMap (roundtripForwardData A) f))
    rw [tComp_id_right, tComp_id_left, roundtrip_unit_map]
  counit_natural f := by
    change tComp (ofOldSupercategory (legacyCategory A)).data
      (tMap (roundtripForwardData A) (tMap (roundtripBackwardData A) f))
      (evenPoint ((ofOldSupercategory (legacyCategory A)).data.id _)) =
      tComp (ofOldSupercategory (legacyCategory A)).data
        (evenPoint ((ofOldSupercategory (legacyCategory A)).data.id _)) f
    rw [tComp_id_right, tComp_id_left, roundtrip_counit_map]
  tensor_natural f g := by
    change tComp (ofOldSupercategory (legacyCategory A)).data _
      (evenPoint ((ofOldSupercategory (legacyCategory A)).data.id _)) =
      tComp (ofOldSupercategory (legacyCategory A)).data
        (evenPoint ((ofOldSupercategory (legacyCategory A)).data.id _)) _
    rw [tComp_id_right, tComp_id_left]
    apply (totalHomEquiv (legacyCategory A) _ _).injective
    exact (roundtripForward_tensor A f g).trans (roundtripForward_total A _).symm
  associativity X Y Z := by
    change (𝟙 _ ▷ _) ≫ 𝟙 _ ≫
      (Superfunctor.enriched (roundtripForward A)).forget.map (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫ (_ ◁ 𝟙 _) ≫ 𝟙 _
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    apply (evenHomEquiv (legacyCategory A) _ _).injective
    apply WideSubcategory.hom_ext
    exact (roundtripForward_even A (α_ X Y Z).hom).trans
      (oldValue_associator (legacyCategory A) X Y Z).symm
  left_unit X := by
    change (𝟙 _ ▷ _) ≫ 𝟙 _ ≫
      (Superfunctor.enriched (roundtripForward A)).forget.map (λ_ X).hom = (λ_ _).hom
    simp only [id_whiskerRight, Category.id_comp]
    apply (evenHomEquiv (legacyCategory A) _ _).injective
    apply WideSubcategory.hom_ext
    exact (roundtripForward_even A (λ_ X).hom).trans
      (oldValue_leftUnitor (legacyCategory A) X).symm
  right_unit X := by
    change (_ ◁ 𝟙 _) ≫ 𝟙 _ ≫
      (Superfunctor.enriched (roundtripForward A)).forget.map (ρ_ X).hom = (ρ_ _).hom
    simp only [whiskerLeft_id, Category.id_comp]
    apply (evenHomEquiv (legacyCategory A) _ _).injective
    apply WideSubcategory.hom_ext
    exact (roundtripForward_even A (ρ_ X).hom).trans
      (oldValue_rightUnitor (legacyCategory A) X).symm

def roundtripEquivalence : MonoidalSuperequivalence
    A.toMonoidalPiSupercategory.monoidal (ofOldMonoidalSupercategory (legacyCategory A)) :=
  ⟨roundtripEquivalenceData A, roundtripEquivalenceLaws A⟩

end RMod.Legacy.Hierarchy
