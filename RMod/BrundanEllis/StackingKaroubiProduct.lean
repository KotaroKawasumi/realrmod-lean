import RMod.BrundanEllis.StackingKaroubiEnrichment
import RMod.BrundanEllis.StackingProductWhisker

/-! Pairing two idempotent corners gives a corner of the super product.
The Hom map includes both corner factors and then restricts to their product
projector, retaining the Koszul interchange in composition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable {A B : Type} [SuperCategory A] [SuperCategory B]

def pairObject (P : Karoubi (Even A)) (Q : Karoubi (Even B)) :
    Karoubi (Even (SuperTensorProduct A B)) where
  X := (productPair A B).obj (P.X, Q.X)
  p := (productPair A B).map (X := (P.X, Q.X)) (Y := (P.X, Q.X)) (P.p, Q.p)
  idem := by
    rw [← Functor.map_comp]
    change (productPair A B).map (X := (P.X, Q.X)) (Y := (P.X, Q.X)) (P.p ≫ P.p, Q.p ≫ Q.p) = _
    rw [P.idem, Q.idem]

theorem pair_projector (P P' : Karoubi (Even A)) (Q Q' : Karoubi (Even B)) :
    projector (pairObject P Q) (pairObject P' Q') = projector P P' ⊗ₘ projector Q Q' := by
  change eHomWhiskerRight SuperVec
      ((productPair A B).map (X := (P.X, Q.X)) (Y := (P.X, Q.X)) (P.p, Q.p))
      ((productPair A B).obj (P'.X, Q'.X)) ≫
    eHomWhiskerLeft SuperVec ((productPair A B).obj (P.X, Q.X))
      ((productPair A B).map (X := (P'.X, Q'.X)) (Y := (P'.X, Q'.X)) (P'.p, Q'.p)) = _
  rw [product_whisker_right, product_whisker_left, tensorHom_comp_tensorHom]
  rfl

def pairHom (P P' : Karoubi (Even A)) (Q Q' : Karoubi (Even B)) :
    homObject P P' ⊗ homObject Q Q' ⟶ homObject (pairObject P Q) (pairObject P' Q') :=
  (inclusion P P' ⊗ₘ inclusion Q Q') ≫ restriction (pairObject P Q) (pairObject P' Q')

@[reassoc] theorem pairHom_inclusion (P P' : Karoubi (Even A)) (Q Q' : Karoubi (Even B)) :
    pairHom P P' Q Q' ≫ inclusion (pairObject P Q) (pairObject P' Q') =
      inclusion P P' ⊗ₘ inclusion Q Q' := by
  rw [pairHom, assoc, restriction_inclusion, pair_projector, tensorHom_comp_tensorHom,
    inclusion_projector, inclusion_projector]

/-- The enriched pairing of corners, before applying any monoidal tensor. -/
def pairFunctor :
    SuperFunctor (SuperTensorProduct (Karoubi (Even A)) (Karoubi (Even B)))
      (Karoubi (Even (SuperTensorProduct A B))) where
  obj X := pairObject X.1 X.2
  map X Y := pairHom X.1 Y.1 X.2 Y.2
  map_id X := by
    apply (cancel_mono (inclusion (pairObject X.1 X.2) (pairObject X.1 X.2))).1
    change ((λ_ (𝟙_ SuperVec)).inv ≫ (identity X.1 ⊗ₘ identity X.2) ≫
        pairHom X.1 X.1 X.2 X.2) ≫ inclusion (pairObject X.1 X.2) (pairObject X.1 X.2) =
      identity (pairObject X.1 X.2) ≫ inclusion (pairObject X.1 X.2) (pairObject X.1 X.2)
    simp only [assoc, pairHom_inclusion, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, identity_inclusion]
    exact (productPair_map_homTo (A := A) (B := B) (X := (X.1.X, X.2.X))
      (Y := (X.1.X, X.2.X)) (X.1.p, X.2.p)).symm
  map_comp X Y Z := by
    rcases X with ⟨P, Q⟩
    rcases Y with ⟨R, S⟩
    rcases Z with ⟨T, U⟩
    apply (cancel_mono (inclusion (pairObject P Q) (pairObject T U))).1
    change ((tensorμ _ _ _ _ ≫ (composition P R T ⊗ₘ composition Q S U)) ≫
        pairHom P T Q U) ≫ inclusion (pairObject P Q) (pairObject T U) =
      ((pairHom P R Q S ⊗ₘ pairHom R T S U) ≫
        composition (pairObject P Q) (pairObject R S) (pairObject T U)) ≫
          inclusion (pairObject P Q) (pairObject T U)
    simp only [assoc, pairHom_inclusion, composition_inclusion,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom, composition_inclusion_assoc]
    change tensorμ _ _ _ _ ≫
        (((inclusion P R ⊗ₘ inclusion R T) ≫ eComp SuperVec P.X R.X T.X) ⊗ₘ
          ((inclusion Q S ⊗ₘ inclusion S U) ≫ eComp SuperVec Q.X S.X U.X)) =
      ((inclusion P R ⊗ₘ inclusion Q S) ⊗ₘ
        (inclusion R T ⊗ₘ inclusion S U)) ≫ tensorμ _ _ _ _ ≫
          (eComp SuperVec P.X R.X T.X ⊗ₘ eComp SuperVec Q.X S.X U.X)
    rw [← tensorHom_comp_tensorHom, ← assoc, ← tensorμ_natural, assoc]

end RMod.BrundanEllis.Stacking.KaroubiSuper
