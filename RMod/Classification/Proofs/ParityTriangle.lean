import RMod.Classification.Proofs.ZeroParityPentagon

/-!
# The local triangle with the normalized supported unit

The middle group label is the identity. Its two adjacent parity entries
are zero and the remaining two agree. The local triangle is therefore
ordinary unit coherence, even when the surviving parity factor is odd.
The unit maps delete the actual right unit factor before applying C's
left or right unitor, exactly as in the pullback construction.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem factorEven_one : evenObj ℝ (LinearCategory C) (p.factor 1) =
    evenObj ℝ (LinearCategory C) p.object := rfl

theorem multiplyFactorsEven_zero_one :
    IsoData.toEvenIso C (p.multiplyFactors 0 1) (hp.multiplyFactors_evenIso C.laws 0 1) =
      λ_ (evenObj ℝ (LinearCategory C) p.object) := rfl

theorem scalarFreeAssociatorEven_triangle (X Y : EvenSubcategory ℝ (LinearCategory C)) (a : ZMod 2) :
    (scalarFreeAssociatorEvenIso C p hp X (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) Y 0 a 0 a rfl).hom ≫
        ((𝟙 X ⊗ₘ ((ρ_ ((𝟙_ (EvenSubcategory ℝ (LinearCategory C))) ⊗ Y)).hom ≫ (λ_ Y).hom)) ⊗ₘ
          𝟙 (evenObj ℝ (LinearCategory C) (p.factor a))) =
      ((((ρ_ (X ⊗ 𝟙_ (EvenSubcategory ℝ (LinearCategory C)))).hom ≫ (ρ_ X).hom) ⊗ₘ 𝟙 Y) ⊗ₘ
        𝟙 (evenObj ℝ (LinearCategory C) (p.factor a))) := by
  rcases parity_cases a with rfl | rfl
  · unfold scalarFreeAssociatorEvenIso normalLeftEvenIso normalRightEvenIso
    rw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero C p hp]
    simp only [eqToIso_refl, factorEven_zero C p]
    monoidal_coherence
  · unfold scalarFreeAssociatorEvenIso normalLeftEvenIso normalRightEvenIso
    rw [moveFactorEven_zero C p hp, multiplyFactorsEven_zero_one C p hp]
    simp only [eqToIso_refl, factorEven_zero C p, factorEven_one C p]
    monoidal_coherence

include hp

theorem localAssociator_triangle (X Y : C.data.Obj) (a : ZMod 2) :
    C.data.comp (p.localAssociator X C.data.tensorUnit Y 0 a 0 a rfl 1).hom
      (C.data.tensorHom
        (C.data.tensorHom (C.data.id X)
          (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y))
            (C.data.leftUnitorHom Y))) (C.data.id (p.factor a))) =
    C.data.tensorHom
      (C.data.tensorHom
        (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj X C.data.tensorUnit))
          (C.data.rightUnitorHom X)) (C.data.id Y)) (C.data.id (p.factor a)) := by
  have he := congrArg (fun f => f.hom) (scalarFreeAssociatorEven_triangle C p hp
    (evenObj ℝ (LinearCategory C) X) (evenObj ℝ (LinearCategory C) Y) a)
  change C.data.comp
    (scalarFreeAssociatorEvenIso C p hp (evenObj ℝ (LinearCategory C) X)
      (𝟙_ (EvenSubcategory ℝ (LinearCategory C))) (evenObj ℝ (LinearCategory C) Y) 0 a 0 a rfl).hom.hom
    (C.data.tensorHom (C.data.tensorHom (C.data.id X)
      (C.data.comp (C.data.rightUnitorHom (C.data.tensorObj C.data.tensorUnit Y))
        (C.data.leftUnitorHom Y))) (C.data.id (p.factor a))) = _ at he
  rw [scalarFreeAssociatorEvenIso_hom] at he
  exact he

end RMod.Classification
