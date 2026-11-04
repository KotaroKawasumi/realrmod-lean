import RMod.BrundanEllis.StackingParityRedistribution
import RMod.BrundanEllis.StackingSignedIsoNaturality

/-! Naturality of parity redistribution, including all signs before their
cancellation.  The input and output morphisms have the same total degree. -/
set_option autoImplicit false
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- The inverse parity deletion has the same sign as deletion. -/
theorem rightFactorInsertion_naturality {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {P : PiData C} (hP : PiLaws C P)
    {X Y : C.Obj} (a i : ZMod 2) (f : C.Hom X Y) (hf : C.IsHomogeneous i f) :
    C.comp f (P.rightFactorDeletion Y a).inv =
      C.smul ((-1 : ℝ) ^ (a * i).val)
        (C.comp (P.rightFactorDeletion X a).inv (C.tensorHom f (C.id (P.factor a)))) :=
  signedIsoNaturality_symm hC
    (hP.rightFactorDeletion_homogeneousIso hC X a).toIsoLaws
    (hP.rightFactorDeletion_homogeneousIso hC Y a).toIsoLaws _ (parity_power_mul_self _)
    (hP.rightFactorDeletion_naturality hC a f hf)

/-- Inserting two parity factors contributes their sum times the total degree. -/
theorem parityInsertions_naturality {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {P : PiData C} (hP : PiLaws C P)
    {V V' W W' : C.Obj} (p q j k : ZMod 2)
    (g : C.Hom V V') (h : C.Hom W W') (hg : C.IsHomogeneous j g) (hh : C.IsHomogeneous k h) :
    C.comp (C.tensorHom g h)
      (C.tensorHom (P.rightFactorDeletion V' q).inv (P.rightFactorDeletion W' p).inv) =
    C.smul ((-1 : ℝ) ^ ((p + q) * (j + k)).val)
      (C.comp (C.tensorHom (P.rightFactorDeletion V q).inv (P.rightFactorDeletion W p).inv)
        (C.tensorHom (C.tensorHom g (C.id (P.factor q))) (C.tensorHom h (C.id (P.factor p))))) := by
  have ht := signedIsoNaturality_tensor hC
    (d := (P.rightFactorDeletion V q).symm C) (d' := (P.rightFactorDeletion V' q).symm C)
    (e := (P.rightFactorDeletion W p).symm C) (e' := (P.rightFactorDeletion W' p).symm C)
    q p j k _ _
    (hP.rightFactorDeletion_homogeneousIso hC V q).inv_grade
    (hP.rightFactorDeletion_homogeneousIso hC W' p).inv_grade hg
    (by
      change C.tensorHom h (C.id (P.factor p)) ∈ C.grade _ _ k
      simpa only [add_zero] using hC.tensor_grade h (C.id (P.factor p)) hh (hC.id_even _))
    (rightFactorInsertion_naturality hC hP q j g hg)
    (rightFactorInsertion_naturality hC hP p k h hh)
  have hs : (((-1 : ℝ) ^ (p * j).val * (-1 : ℝ) ^ (q * j).val *
      (-1 : ℝ) ^ (p * k).val) * (-1 : ℝ) ^ (k * q).val) =
      (-1 : ℝ) ^ ((p + q) * (j + k)).val := by
    simp only [← parity_power_add]
    congr 2
    ring
  rw [hs] at ht
  exact ht

/-- Redistribution cancels every insertion sign except the comparison degree. -/
theorem parityRedistribution_naturality {C : WeaklyPointedSuperfusionData.{u, v}}
    (hC : WeaklyPointedSuperfusionLaws C) {P : PiData C} (hP : PiLaws C P)
    {U U' V V' W W' : C.Obj} (p q c j k : ZMod 2)
    (e : IsoData C U (C.tensorObj V W)) (e' : IsoData C U' (C.tensorObj V' W'))
    (f : C.Hom U U') (g : C.Hom V V') (h : C.Hom W W')
    (hf : C.IsHomogeneous (j + k) f) (hg : C.IsHomogeneous j g) (hh : C.IsHomogeneous k h)
    (r : ℝ) (hn : C.comp f e'.hom = C.smul r (C.comp e.hom (C.tensorHom g h))) :
    C.comp (C.tensorHom f (C.id (P.factor (p + q + c))))
      (parityRedistributionData C P U' V' W' p q c e').hom =
    C.smul (((-1 : ℝ) ^ (c * (j + k)).val) * r)
      (C.comp (parityRedistributionData C P U V W p q c e).hom
        (C.tensorHom (C.tensorHom g (C.id (P.factor q))) (C.tensorHom h (C.id (P.factor p))))) := by
  have h₁ := hP.rightFactorDeletion_naturality hC (p + q + c) f hf
  have h₂ := parityInsertions_naturality hC hP p q j k g h hg hh
  have ht := signedIsoNaturality_trans hC _ _
    (signedIsoNaturality_trans hC _ _ h₁ hn)
    (d := ((P.rightFactorDeletion U (p + q + c)).trans C e))
    (d' := ((P.rightFactorDeletion U' (p + q + c)).trans C e'))
    (e := ((P.rightFactorDeletion V q).symm C).homogeneousTensor C q p
      ((P.rightFactorDeletion W p).symm C))
    (e' := ((P.rightFactorDeletion V' q).symm C).homogeneousTensor C q p
      ((P.rightFactorDeletion W' p).symm C)) h₂
  have hs : (((-1 : ℝ) ^ ((p + q + c) * (j + k)).val) * r) *
      (-1 : ℝ) ^ ((p + q) * (j + k)).val = (-1 : ℝ) ^ (c * (j + k)).val * r := by
    rw [mul_right_comm, ← parity_power_add]
    congr 2
    ring_nf
    simp [CharTwo.two_eq_zero]
  rw [hs] at ht
  exact ht

end RMod.BrundanEllis.Stacking
