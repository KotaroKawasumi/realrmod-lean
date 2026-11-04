import RMod.Classification.Proofs.IsoNaturality
import RMod.Classification.Proofs.ParityPowers

/-! Scalar naturality squares compose and tensor.  The tensor law keeps
both interchange signs, allowing odd structural exchanges to be combined
with ordinary even associators. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification
variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C)
include hC

/-- Composing two scalar naturality squares multiplies their scalars. -/
theorem signedIsoNaturality_trans {X Y Z X' Y' Z' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {e : IsoData C Y Z} {e' : IsoData C Y' Z'}
    {f : C.Hom X X'} {g : C.Hom Y Y'} {h : C.Hom Z Z'} (r s : ℝ)
    (hd : C.comp f d'.hom = C.smul r (C.comp d.hom g))
    (he : C.comp g e'.hom = C.smul s (C.comp e.hom h)) :
    C.comp f (d'.trans C e').hom = C.smul (r * s) (C.comp (d.trans C e).hom h) := by
  change C.comp f (C.comp d'.hom e'.hom) = C.smul (r * s) (C.comp (C.comp d.hom e.hom) h)
  rw [← hC.comp_assoc, hd, hC.smul_comp, hC.comp_assoc, he,
    hC.comp_smul, ← hC.mul_smul, ← hC.comp_assoc]

/-- An involutive scalar is unchanged when a naturality square is inverted. -/
theorem signedIsoNaturality_symm {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    (hd : IsoLaws C d) (hd' : IsoLaws C d')
    {f : C.Hom X X'} {g : C.Hom Y Y'} (r : ℝ) (hr : r * r = 1)
    (he : C.comp f d'.hom = C.smul r (C.comp d.hom g)) :
    C.comp g (d'.symm C).hom = C.smul r (C.comp (d.symm C).hom f) := by
  change C.comp g d'.inv = C.smul r (C.comp d.inv f)
  have hh := congrArg (fun q => C.comp d.inv (C.comp q d'.inv)) he
  simp only [hC.smul_comp, hC.comp_smul, hC.comp_assoc, hd'.hom_inv, hC.comp_id,
    ← hC.comp_assoc d.inv d.hom, hd.inv_hom, hC.id_comp] at hh
  have hh' := congrArg (C.smul r) hh
  simpa only [← hC.mul_smul, hr, hC.one_smul] using hh'.symm

/-- Tensoring scalar squares adds the two necessary Koszul crossing signs. -/
theorem signedIsoNaturality_tensor {X Y Z W X' Y' Z' W' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {e : IsoData C Z W} {e' : IsoData C Z' W'}
    {f : C.Hom X X'} {g : C.Hom Y Y'} {h : C.Hom Z Z'} {k : C.Hom W W'}
    (a b i l : ZMod 2) (r s : ℝ)
    (hd : C.IsHomogeneous a d.hom) (he' : C.IsHomogeneous b e'.hom)
    (hf : C.IsHomogeneous i f) (hk : C.IsHomogeneous l k)
    (hdn : C.comp f d'.hom = C.smul r (C.comp d.hom g))
    (hen : C.comp h e'.hom = C.smul s (C.comp e.hom k)) :
    C.comp (C.tensorHom f h) (d'.tensor C e').hom =
      C.smul (((-1 : ℝ) ^ (b * i).val * r * s) * (-1 : ℝ) ^ (l * a).val)
        (C.comp (d.tensor C e).hom (C.tensorHom g k)) := by
  change C.comp (C.tensorHom f h) (C.tensorHom d'.hom e'.hom) =
    C.smul _ (C.comp (C.tensorHom d.hom e.hom) (C.tensorHom g k))
  rw [hC.super_interchange d'.hom e'.hom f h he' hf,
    hC.super_interchange g k d.hom e.hom hk hd, hdn, hen,
    hC.tensor_smul_left, hC.tensor_smul_right]
  simp only [← hC.mul_smul]
  rw [mul_assoc _ ((-1 : ℝ) ^ (l * a).val), parity_power_mul_self, mul_one]
  rw [mul_assoc]

/-- Ordinary naturality is the scalar square with coefficient one. -/
theorem isoNaturality_scalar_one {X Y X' Y' : C.Obj}
    {d : IsoData C X Y} {d' : IsoData C X' Y'}
    {f : C.Hom X X'} {g : C.Hom Y Y'}
    (h : C.comp f d'.hom = C.comp d.hom g) :
    C.comp f d'.hom = C.smul 1 (C.comp d.hom g) := by
  rw [hC.one_smul]
  exact h

end RMod.BrundanEllis.Stacking
