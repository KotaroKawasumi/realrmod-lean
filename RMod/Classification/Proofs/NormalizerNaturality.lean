import RMod.Classification.Proofs.IsoNaturality
import RMod.Classification.Proofs.Normalizers
import RMod.Classification.Proofs.CentralNaturality

/-!
# Naturality of the right-parity normalizers

Each normalizer is the specified finite composite of even comparisons.
Naturality is assembled from the individual squares using the full-Hom
tensor calculus, so no evenness restriction is imposed on the input maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem moveFactor_naturality (a : ZMod 2) {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp (C.tensorHom (C.id (p.factor a)) f) (p.moveFactor a Y).hom =
      C.comp (p.moveFactor a X).hom (C.tensorHom f (C.id (p.factor a))) := by
  rcases parity_cases a with rfl | rfl
  · change C.comp (C.tensorHom (C.id C.tensorUnit) f)
      ((IsoData.leftUnit C Y).trans C ((IsoData.rightUnit C Y).symm C)).hom =
      C.comp ((IsoData.leftUnit C X).trans C ((IsoData.rightUnit C X).symm C)).hom
        (C.tensorHom f (C.id C.tensorUnit))
    exact iso_naturality_trans hC (hC.left_unitor_naturality f)
      (iso_naturality_symm hC (EvenIsoLaws.rightUnit hC X).toIsoLaws
        (EvenIsoLaws.rightUnit hC Y).toIsoLaws (hC.right_unitor_naturality f))
  · exact hp.central_naturality hC f

theorem normalRight_naturality {X Y Z X' Y' Z' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (h : C.Hom Z Z') (a b : ZMod 2) :
    C.comp (C.tensorHom (C.tensorHom f (C.tensorHom (C.tensorHom g h) (C.id (p.factor a))))
      (C.id (p.factor b))) (p.normalRight X' Y' Z' a b).hom =
    C.comp (p.normalRight X Y Z a b).hom
      (C.tensorHom (C.tensorHom f (C.tensorHom g h)) (C.id (p.factor (a + b)))) := by
  let P := p.factor a
  let Q := p.factor b
  let U := C.tensorObj X (C.tensorObj Y Z)
  have h₁ := iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC X (C.tensorObj Y Z) P).symm
    (iso_naturality_symm hC (EvenIsoLaws.assoc hC X (C.tensorObj Y Z) P).toIsoLaws
      (EvenIsoLaws.assoc hC X' (C.tensorObj Y' Z') P).toIsoLaws
      (hC.associator_naturality f (C.tensorHom g h) (C.id P))) Q
  have h₂ := hC.associator_naturality (C.tensorHom f (C.tensorHom g h)) (C.id P) (C.id Q)
  rw [hC.tensor_id] at h₂
  have h₃ := iso_naturality_tensor hC (EvenIsoLaws.refl hC U)
    (hp.multiplyFactors_evenIso hC a b)
    (iso_naturality_refl hC (C.tensorHom f (C.tensorHom g h)))
    (iso_naturality_constant hC (p.multiplyFactors a b))
  exact iso_naturality_trans hC (iso_naturality_trans hC h₁ h₂) h₃

theorem normalLeft_naturality {X Y Z X' Y' Z' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (h : C.Hom Z Z') (a b : ZMod 2) :
    C.comp (C.tensorHom (C.tensorHom (C.tensorHom (C.tensorHom f g) (C.id (p.factor a))) h)
      (C.id (p.factor b))) (p.normalLeft X' Y' Z' a b).hom =
    C.comp (p.normalLeft X Y Z a b).hom
      (C.tensorHom (C.tensorHom f (C.tensorHom g h)) (C.id (p.factor (a + b)))) := by
  let P := p.factor a
  let Q := p.factor b
  let U := C.tensorObj X (C.tensorObj Y Z)
  have h₁ := iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC (C.tensorObj X Y) P Z)
    (d' := IsoData.assoc C (C.tensorObj X' Y') P Z')
    (hC.associator_naturality (C.tensorHom f g) (C.id P) h) Q
  have h₂ := iso_naturality_whiskerRight hC
    ((EvenIsoLaws.refl hC (C.tensorObj X Y)).tensor hC (hp.moveFactor_evenIso hC a Z))
    (iso_naturality_tensor hC (EvenIsoLaws.refl hC (C.tensorObj X Y))
      (hp.moveFactor_evenIso hC a Z') (iso_naturality_refl hC (C.tensorHom f g))
      (hp.moveFactor_naturality hC a h)) Q
  have h₃ := iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC (C.tensorObj X Y) Z P).symm
    (iso_naturality_symm hC (EvenIsoLaws.assoc hC (C.tensorObj X Y) Z P).toIsoLaws
      (EvenIsoLaws.assoc hC (C.tensorObj X' Y') Z' P).toIsoLaws
      (hC.associator_naturality (C.tensorHom f g) h (C.id P))) Q
  have h₄ := iso_naturality_whiskerRight hC
    ((EvenIsoLaws.assoc hC X Y Z).tensor hC (EvenIsoLaws.refl hC P))
    (iso_naturality_whiskerRight hC (EvenIsoLaws.assoc hC X Y Z)
      (d' := IsoData.assoc C X' Y' Z')
      (hC.associator_naturality f g h) P) Q
  have h₅ := hC.associator_naturality (C.tensorHom f (C.tensorHom g h)) (C.id P) (C.id Q)
  rw [hC.tensor_id] at h₅
  have h₆ := iso_naturality_tensor hC (EvenIsoLaws.refl hC U)
    (hp.multiplyFactors_evenIso hC a b)
    (iso_naturality_refl hC (C.tensorHom f (C.tensorHom g h)))
    (iso_naturality_constant hC (p.multiplyFactors a b))
  exact iso_naturality_trans hC
    (iso_naturality_trans hC (iso_naturality_trans hC (iso_naturality_trans hC
      (iso_naturality_trans hC h₁ h₂) h₃) h₄) h₅) h₆

theorem localAssociator_naturality {X Y Z X' Y' Z' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (h : C.Hom Z Z')
    (a b c d : ZMod 2) (he : a + b = c + d) (omega : ℝˣ) :
    C.comp (C.tensorHom (C.tensorHom (C.tensorHom (C.tensorHom f g) (C.id (p.factor a))) h)
      (C.id (p.factor b))) (p.localAssociator X' Y' Z' a b c d he omega).hom =
    C.comp (p.localAssociator X Y Z a b c d he omega).hom
      (C.tensorHom (C.tensorHom f (C.tensorHom (C.tensorHom g h) (C.id (p.factor c))))
        (C.id (p.factor d))) := by
  have hL := hp.normalLeft_naturality hC f g h a b
  have hR := hp.normalRight_naturality hC f g h c d
  have hE := iso_naturality_tensor_ofEq hC (congrArg p.factor he) (C.tensorHom f (C.tensorHom g h))
  have hRi := iso_naturality_symm hC (hp.normalRight_evenIso hC X Y Z c d).toIsoLaws
    (hp.normalRight_evenIso hC X' Y' Z' c d).toIsoLaws hR
  exact iso_naturality_scale hC (iso_naturality_trans hC hL
    (iso_naturality_trans hC hE hRi)) omega

end RMod.Classification.PiLaws
