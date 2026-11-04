import RMod.BrundanEllis.StackingKaroubiEvenMonoidal
import RMod.BrundanEllis.StackingKaroubiWhisker

/-! Concrete maps of the equivalence between the even enriched completion
and ordinary Karoubi. Its transported tensor and structural isomorphisms map
to the corresponding ordinary Karoubi operations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {C : Type} [SuperCategory C]

/-- Typed Hom notation for the even view of a corner. -/
abbrev evenHom (P Q : Even (Karoubi (Even C))) : SuperVec :=
  homObject (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q)
abbrev evenInclusion (P Q : Even (Karoubi (Even C))) :
    evenHom P Q ⟶ ((ForgetEnrichment.to SuperVec P).X ⟶[SuperVec] (ForgetEnrichment.to SuperVec Q).X) :=
  inclusion (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q)

theorem even_map_point {P Q : Even (Karoubi (Even C))} (f : P ⟶ Q) :
    eHomEquiv SuperVec ((evenEquivalence (C := C)).functor.map f) =
      ForgetEnrichment.homTo SuperVec f :=
  (homEquivalence (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q)).apply_symm_apply _

@[reassoc] theorem even_hom_inclusion {P Q : Even (Karoubi (Even C))} (f : P ⟶ Q) :
    ForgetEnrichment.homTo SuperVec f ≫ inclusion (ForgetEnrichment.to SuperVec P)
        (ForgetEnrichment.to SuperVec Q) =
      eHomEquiv SuperVec ((evenEquivalence (C := C)).functor.map f).f := by
  exact ((eHomEquiv SuperVec (C := Even C)).apply_symm_apply _).symm

theorem even_map_inverse {P Q : Karoubi (Even C)} (f : P ⟶ Q) :
    (evenEquivalence (C := C)).functor.map ((evenEquivalence (C := C)).inverse.map f) = f :=
  (homEquivalence P Q).left_inv f

theorem even_whisker_post (P : Even (Karoubi (Even C)))
    {Q R : Even (Karoubi (Even C))} (f : Q ⟶ R) :
    eHomWhiskerLeft SuperVec P f =
      eHomWhiskerLeft SuperVec (ForgetEnrichment.to SuperVec P)
        ((evenEquivalence (C := C)).functor.map f) := by
  change (ρ_ (homObject P Q)).inv ≫ _ ◁ ForgetEnrichment.homTo SuperVec f ≫ composition P Q R =
    (ρ_ (homObject P Q)).inv ≫ _ ◁
      eHomEquiv SuperVec ((evenEquivalence (C := C)).functor.map f) ≫ composition P Q R
  rw [even_map_point]

theorem even_whisker_pre {P Q : Even (Karoubi (Even C))} (f : P ⟶ Q)
    (R : Even (Karoubi (Even C))) :
    eHomWhiskerRight SuperVec f R =
      eHomWhiskerRight SuperVec ((evenEquivalence (C := C)).functor.map f)
        (ForgetEnrichment.to SuperVec R) := by
  change (λ_ (homObject Q R)).inv ≫ ForgetEnrichment.homTo SuperVec f ▷ _ ≫ composition P Q R =
    (λ_ (homObject Q R)).inv ≫
      eHomEquiv SuperVec ((evenEquivalence (C := C)).functor.map f) ▷ _ ≫ composition P Q R
  rw [even_map_point]

variable [MonoidalCategory (Even C)]

theorem even_tensor_map {P P' Q Q' : Even (Karoubi (Even C))}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (evenEquivalence (C := C)).functor.map (f ⊗ₘ g) =
      (evenEquivalence (C := C)).functor.map f ⊗ₘ (evenEquivalence (C := C)).functor.map g := by
  exact even_map_inverse _

theorem even_associator_map (P Q R : Even (Karoubi (Even C))) :
    (evenEquivalence (C := C)).functor.map (α_ P Q R).hom =
      (α_ (ForgetEnrichment.to SuperVec P) (ForgetEnrichment.to SuperVec Q)
        (ForgetEnrichment.to SuperVec R)).hom := by
  let p := ForgetEnrichment.to SuperVec P
  let q := ForgetEnrichment.to SuperVec Q
  let r := ForgetEnrichment.to SuperVec R
  change (evenEquivalence (C := C)).functor.map ((evenEquivalence (C := C)).inverse.map
    ((𝟙 (p ⊗ q) ▷ r) ≫ (α_ p q r).hom ≫ (p ◁ 𝟙 (q ⊗ r)))) = _
  rw [even_map_inverse, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]

theorem even_leftUnitor_map (P : Even (Karoubi (Even C))) :
    (evenEquivalence (C := C)).functor.map (λ_ P).hom =
      (λ_ (ForgetEnrichment.to SuperVec P)).hom := by
  let p := ForgetEnrichment.to SuperVec P
  change (evenEquivalence (C := C)).functor.map
    ((evenEquivalence (C := C)).inverse.map ((𝟙 (𝟙_ (Karoubi (Even C))) ▷ p) ≫ (λ_ p).hom) ≫ 𝟙 ((evenEquivalence (C := C)).inverse.obj p)) = _
  rw [Category.comp_id, even_map_inverse, id_whiskerRight, Category.id_comp]

theorem even_rightUnitor_map (P : Even (Karoubi (Even C))) :
    (evenEquivalence (C := C)).functor.map (ρ_ P).hom =
      (ρ_ (ForgetEnrichment.to SuperVec P)).hom := by
  let p := ForgetEnrichment.to SuperVec P
  change (evenEquivalence (C := C)).functor.map
    ((evenEquivalence (C := C)).inverse.map ((p ◁ 𝟙 (𝟙_ (Karoubi (Even C)))) ≫ (ρ_ p).hom) ≫ 𝟙 ((evenEquivalence (C := C)).inverse.obj p)) = _
  rw [Category.comp_id, even_map_inverse, whiskerLeft_id, Category.id_comp]

end RMod.BrundanEllis.Stacking.KaroubiSuper
