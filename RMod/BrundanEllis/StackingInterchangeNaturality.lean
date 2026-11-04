import RMod.BrundanEllis.StackingSignedIsoNaturality
import RMod.BrundanEllis.StackingInterchangeIso

/-! Naturality of the four-factor interchange.  The middle scalar square
is transported through the even associators, and the two outer factors
contribute exactly their Koszul signs with the middle exchange. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Naturality of interchange with a homogeneous middle exchange. -/
theorem interchangeIsoNaturality {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {X X' Y Y' Z Z' W W' : C.Obj}
    (f : C.Hom X X') (g : C.Hom Y Y') (h : C.Hom Z Z') (k : C.Hom W W')
    (d : IsoData C (C.tensorObj Y Z) (C.tensorObj Z Y))
    (d' : IsoData C (C.tensorObj Y' Z') (C.tensorObj Z' Y'))
    (a i j l m : ZMod 2) (r : ℝ)
    (hd : C.IsHomogeneous a d.hom) (hd' : C.IsHomogeneous a d'.hom)
    (hf : C.IsHomogeneous i f) (hg : C.IsHomogeneous j g)
    (hh : C.IsHomogeneous l h) (hk : C.IsHomogeneous m k)
    (hn : C.comp (C.tensorHom g h) d'.hom = C.smul r (C.comp d.hom (C.tensorHom h g))) :
    C.comp (C.tensorHom (C.tensorHom f g) (C.tensorHom h k))
      (interchangeIsoData C X' Y' Z' W' d').hom =
    C.smul (((-1 : ℝ) ^ (a * i).val * r) * (-1 : ℝ) ^ (m * a).val)
      (C.comp (interchangeIsoData C X Y Z W d).hom
        (C.tensorHom (C.tensorHom f h) (C.tensorHom g k))) := by
  have h₁ := isoNaturality_scalar_one hC
    (d := IsoData.assoc C X Y (C.tensorObj Z W))
    (d' := IsoData.assoc C X' Y' (C.tensorObj Z' W'))
    (hC.associator_naturality f g (C.tensorHom h k))
  have h₂ := isoNaturality_scalar_one hC
    (iso_naturality_tensor hC (EvenIsoLaws.refl hC X)
      (EvenIsoLaws.assoc hC Y' Z' W').symm (iso_naturality_refl hC f)
      (iso_naturality_symm hC (EvenIsoLaws.assoc hC Y Z W).toIsoLaws
        (EvenIsoLaws.assoc hC Y' Z' W').toIsoLaws (hC.associator_naturality g h k)))
  have hmiddle := signedIsoNaturality_tensor hC
    (d := d) (d' := d') (e := IsoData.refl C W) (e' := IsoData.refl C W') a 0 (j + l) m r 1
    hd (hC.id_even W') (hC.tensor_grade g h hg hh) hk hn
    (isoNaturality_scalar_one hC (iso_naturality_refl hC k))
  have ht' : C.IsHomogeneous a (d'.tensor C (IsoData.refl C W')).hom := by
    change C.tensorHom d'.hom (C.id W') ∈ C.grade _ _ a
    simpa only [add_zero] using hC.tensor_grade d'.hom (C.id W') hd' (hC.id_even W')
  have h₃ := signedIsoNaturality_tensor hC
    (d := IsoData.refl C X) (d' := IsoData.refl C X')
    (e := d.tensor C (IsoData.refl C W)) (e' := d'.tensor C (IsoData.refl C W'))
    0 a i ((l + j) + m) 1 _
    (hC.id_even X) ht' hf (hC.tensor_grade (C.tensorHom h g) k (hC.tensor_grade h g hh hg) hk)
    (isoNaturality_scalar_one hC (iso_naturality_refl hC f)) hmiddle
  have h₄ := isoNaturality_scalar_one hC
    (iso_naturality_tensor hC (e := IsoData.assoc C Z Y W) (EvenIsoLaws.refl hC X)
      (EvenIsoLaws.assoc hC Z' Y' W') (iso_naturality_refl hC f)
      (hC.associator_naturality h g k))
  have h₅ := isoNaturality_scalar_one hC
    (iso_naturality_symm hC (EvenIsoLaws.assoc hC X Z (C.tensorObj Y W)).toIsoLaws
      (EvenIsoLaws.assoc hC X' Z' (C.tensorObj Y' W')).toIsoLaws
      (hC.associator_naturality f h (C.tensorHom g k)))
  simpa only [interchangeIsoData, zero_mul, mul_zero, ZMod.val_zero, pow_zero,
    one_mul, mul_one, mul_assoc] using
    signedIsoNaturality_trans hC _ _
      (signedIsoNaturality_trans hC _ _ (signedIsoNaturality_trans hC _ _
        (signedIsoNaturality_trans hC _ _ h₁ h₂) h₃) h₄) h₅

end RMod.BrundanEllis.Stacking
