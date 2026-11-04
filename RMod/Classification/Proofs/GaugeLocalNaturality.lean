import RMod.Classification.Proofs.GaugeLocalNormalizers

/-!
# Naturality of the gauge tensorator on the full Hom spaces

The ordinary input maps may be inhomogeneous. Evenness of each structural
step removes the interchange sign when assembling its square. The only
crossing is the specified central half-braiding of the component shift.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightFactorPairNormalizer_naturality {X X' : C.Obj} (f : C.Hom X X') (a b : ZMod 2) :
    C.comp (C.tensorHom (C.tensorHom f (C.id (p.factor a))) (C.id (p.factor b)))
      (p.rightFactorPairNormalizer X' a b).hom =
      C.comp (p.rightFactorPairNormalizer X a b).hom (C.tensorHom f (C.id (p.factor (a + b)))) := by
  have h₁ := hC.associator_naturality f (C.id (p.factor a)) (C.id (p.factor b))
  rw [hC.tensor_id] at h₁
  have h₂ := iso_naturality_tensor hC (EvenIsoLaws.refl hC X)
    (hp.multiplyFactors_evenIso hC a b) (iso_naturality_refl hC f)
    (iso_naturality_constant hC (p.multiplyFactors a b))
  exact iso_naturality_trans hC h₁ h₂

theorem rightFactorTensorNormalizer_naturality {X X' Y Y' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (a b : ZMod 2) :
    C.comp (C.tensorHom (C.tensorHom f (C.id (p.factor a))) (C.tensorHom g (C.id (p.factor b))))
      (p.rightFactorTensorNormalizer X' Y' a b).hom =
      C.comp (p.rightFactorTensorNormalizer X Y a b).hom
        (C.tensorHom (C.tensorHom f g) (C.id (p.factor (a + b)))) := by
  let P := p.factor a
  let Q := p.factor b
  have h₁ := iso_naturality_symm hC
    (EvenIsoLaws.assoc hC (C.tensorObj X P) Y Q).toIsoLaws
    (EvenIsoLaws.assoc hC (C.tensorObj X' P) Y' Q).toIsoLaws
    (hC.associator_naturality (C.tensorHom f (C.id P)) g (C.id Q))
  have h₂ := iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC X P Y)
    (d' := IsoData.assoc C X' P Y') (hC.associator_naturality f (C.id P) g) Q
  have h₃ := iso_naturality_whiskerRight hC
    ((EvenIsoLaws.refl hC X).tensor hC (hp.moveFactor_evenIso hC a Y))
    (iso_naturality_tensor hC (EvenIsoLaws.refl hC X) (hp.moveFactor_evenIso hC a Y')
      (iso_naturality_refl hC f) (hp.moveFactor_naturality hC a g)) Q
  have h₄ := iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC X Y P).symm
    (iso_naturality_symm hC (EvenIsoLaws.assoc hC X Y P).toIsoLaws
      (EvenIsoLaws.assoc hC X' Y' P).toIsoLaws (hC.associator_naturality f g (C.id P))) Q
  have h₅ := hp.rightFactorPairNormalizer_naturality hC (C.tensorHom f g) a b
  exact iso_naturality_trans hC
    (iso_naturality_trans hC (iso_naturality_trans hC (iso_naturality_trans hC h₁ h₂) h₃) h₄) h₅

theorem gaugeSourceNormalizer_naturality {X X' Y Y' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (a b n' : ZMod 2) :
    C.comp (C.tensorHom
      (C.tensorHom (C.tensorHom f (C.id (p.factor a))) (C.tensorHom g (C.id (p.factor b))))
      (C.id (p.factor n'))) (p.gaugeSourceNormalizer X' Y' a b n').hom =
      C.comp (p.gaugeSourceNormalizer X Y a b n').hom
        (C.tensorHom (C.tensorHom f g) (C.id (p.factor ((a + b) + n')))) :=
  iso_naturality_trans hC
    (iso_naturality_whiskerRight hC (hp.rightFactorTensorNormalizer_evenIso hC X Y a b)
      (hp.rightFactorTensorNormalizer_naturality hC f g a b) (p.factor n'))
    (hp.rightFactorPairNormalizer_naturality hC (C.tensorHom f g) (a + b) n')

theorem gaugeLocalTensorator_naturality {X X' Y Y' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (β : ℝˣ) :
    C.comp (C.tensorHom
      (C.tensorHom (C.tensorHom f (C.id (p.factor a))) (C.tensorHom g (C.id (p.factor b))))
      (C.id (p.factor n'))) (p.gaugeLocalTensorator X' Y' a b n' n c e β).hom =
      C.comp (p.gaugeLocalTensorator X Y a b n' n c e β).hom
        (C.tensorHom (C.tensorHom (C.tensorHom f g) (C.id (p.factor n))) (C.id (p.factor c))) :=
  iso_naturality_scale hC
    (iso_naturality_trans hC (hp.gaugeSourceNormalizer_naturality hC f g a b n')
      (iso_naturality_trans hC
        (iso_naturality_tensor_ofEq hC (congrArg p.factor e) (C.tensorHom f g))
        (iso_naturality_symm hC
          (hp.rightFactorPairNormalizer_evenIso hC (C.tensorObj X Y) n c).toIsoLaws
          (hp.rightFactorPairNormalizer_evenIso hC (C.tensorObj X' Y') n c).toIsoLaws
          (hp.rightFactorPairNormalizer_naturality hC (C.tensorHom f g) n c)))) β

end RMod.Classification.PiLaws
