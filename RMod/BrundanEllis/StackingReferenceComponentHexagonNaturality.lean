import RMod.BrundanEllis.StackingReferenceComponentHexagonData
import RMod.BrundanEllis.StackingSignedIsoNaturality
import RMod.BrundanEllis.StackingReferenceScalar

/-! Both routes of each reference hexagon have exactly the same signed
naturality square. The tensor interchange signs are retained even for odd
inclusions, allowing later descent along homogeneous atom presentations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT
local notation "C" => reference.data.toWeaklyPointedSuperfusionData
local notation "L" => referenceProperty.toWeaklyPointedSuperfusionLaws

/-- Compose scalar squares at the level of morphisms. Keeping only the
forward maps avoids choosing irrelevant inverse maps during elaboration. -/
theorem referenceSignedNaturality_comp {X Y Z X' Y' Z' : reference.data.Obj}
    {d : reference.data.Hom X Y} {d' : reference.data.Hom X' Y'}
    {e : reference.data.Hom Y Z} {e' : reference.data.Hom Y' Z'}
    {f : reference.data.Hom X X'} {g : reference.data.Hom Y Y'} {h : reference.data.Hom Z Z'}
    (r s : ℝ)
    (hd : reference.data.comp f d' = reference.data.smul r (reference.data.comp d g))
    (he : reference.data.comp g e' = reference.data.smul s (reference.data.comp e h)) :
    reference.data.comp f (reference.data.comp d' e') =
      reference.data.smul (r * s) (reference.data.comp (reference.data.comp d e) h) := by
  rw [← referenceProperty.toWeaklyPointedSuperfusionLaws.comp_assoc, hd, referenceProperty.toWeaklyPointedSuperfusionLaws.smul_comp, referenceProperty.toWeaklyPointedSuperfusionLaws.comp_assoc, he,
    referenceProperty.toWeaklyPointedSuperfusionLaws.comp_smul, ← referenceProperty.toWeaklyPointedSuperfusionLaws.mul_smul, ← referenceProperty.toWeaklyPointedSuperfusionLaws.comp_assoc]

/-- The exchange degree is additive in each type label. -/
theorem referenceDegree_add_right (a b c : ZMod 8) :
    ReferenceCommutor.degree a (b + c) =
      ReferenceCommutor.degree a b + ReferenceCommutor.degree a c := by
  have hb : ((b + c).val : ZMod 2) = (b.val : ZMod 2) + (c.val : ZMod 2) := by
    change (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) (b + c) = _
    exact map_add _ _ _
  simp only [ReferenceCommutor.degree, hb, mul_add]

theorem referenceDegree_add_left (a b c : ZMod 8) :
    ReferenceCommutor.degree (a + b) c =
      ReferenceCommutor.degree a c + ReferenceCommutor.degree b c := by
  have hb : ((a + b).val : ZMod 2) = (a.val : ZMod 2) + (b.val : ZMod 2) := by
    change (ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)) (a + b) = _
    exact map_add _ _ _
  simp only [ReferenceCommutor.degree, hb, add_mul]

/-- Tensoring an exchange square with an identity keeps the crossing with
that exchange's degree. -/
theorem referenceExchange_whiskerRight_naturality (a b : ZMod 8)
    (X X' Y Y' Z Z' : reference.data.Obj)
    (hX : InComponent C a X) (hX' : InComponent C a X')
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) h)
      ((referenceExchangeData a b X' Y' hX' hY').tensor C (IsoData.refl C Z')).hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree a b * (i + j + k) + i * j))
      (reference.data.comp ((referenceExchangeData a b X Y hX hY).tensor C (IsoData.refl C Z)).hom
        (reference.data.tensorHom (reference.data.tensorHom g f) h)) := by
  have he := signedIsoNaturality_tensor L
    (d := referenceExchangeData a b X Y hX hY)
    (d' := referenceExchangeData a b X' Y' hX' hY')
    (e := IsoData.refl C Z) (e' := IsoData.refl C Z')
    (ReferenceCommutor.degree a b) 0 (i + j) k _ 1
    (referenceExchange_grade a b X Y hX hY) (referenceProperty.toWeaklyPointedSuperfusionLaws.id_even Z')
    (referenceProperty.toWeaklyPointedSuperfusionLaws.tensor_grade f g hf hg) hh
    (referenceExchange_naturality a b X X' Y Y' hX hX' hY hY' f g i j hf hg)
    (isoNaturality_scalar_one L (iso_naturality_refl L h))
  have hs : ((-1 : ℝ) ^ (0 * (i + j) : ZMod 2).val *
      paritySign (ReferenceCommutor.degree a b * (i + j) + i * j) * 1) *
        (-1 : ℝ) ^ (k * ReferenceCommutor.degree a b).val =
      paritySign (ReferenceCommutor.degree a b * (i + j + k) + i * j) := by
    simp only [zero_mul, ZMod.val_zero, pow_zero, one_mul, mul_one,
      ReferenceCommutor.paritySign_pow, ← parity_power_add]
    congr 2
    ring
  rw [hs] at he
  exact he

/-- The analogous square with the identity in the first tensor position. -/
theorem referenceExchange_whiskerLeft_naturality (b c : ZMod 8)
    (X X' Y Y' Z Z' : reference.data.Obj)
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (hZ : InComponent C c Z) (hZ' : InComponent C c Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom f (reference.data.tensorHom g h))
      ((IsoData.refl C X').tensor C (referenceExchangeData b c Y' Z' hY' hZ')).hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree b c * (i + j + k) + j * k))
      (reference.data.comp ((IsoData.refl C X).tensor C (referenceExchangeData b c Y Z hY hZ)).hom
        (reference.data.tensorHom f (reference.data.tensorHom h g))) := by
  have he := signedIsoNaturality_tensor L
    (d := IsoData.refl C X) (d' := IsoData.refl C X')
    (e := referenceExchangeData b c Y Z hY hZ)
    (e' := referenceExchangeData b c Y' Z' hY' hZ')
    0 (ReferenceCommutor.degree b c) i (k + j) 1 _
    (referenceProperty.toWeaklyPointedSuperfusionLaws.id_even X) (referenceExchange_grade b c Y' Z' hY' hZ')
    hf (referenceProperty.toWeaklyPointedSuperfusionLaws.tensor_grade h g hh hg)
    (isoNaturality_scalar_one L (iso_naturality_refl L f))
    (referenceExchange_naturality b c Y Y' Z Z' hY hY' hZ hZ' g h j k hg hh)
  have hs : ((-1 : ℝ) ^ (ReferenceCommutor.degree b c * i).val * 1 *
      paritySign (ReferenceCommutor.degree b c * (j + k) + j * k)) *
        (-1 : ℝ) ^ ((k + j) * 0 : ZMod 2).val =
      paritySign (ReferenceCommutor.degree b c * (i + j + k) + j * k) := by
    simp only [mul_zero, ZMod.val_zero, pow_zero, mul_one,
      ReferenceCommutor.paritySign_pow, ← parity_power_add]
    congr 2
    ring
  rw [hs] at he
  exact he

/-- Signed naturality of the left hexagon short path. -/
theorem referenceLeftHexagonShort_naturality (a b c : ZMod 8) (X X' Y Y' Z Z' : reference.data.Obj)
    (hX : InComponent C a X) (hX' : InComponent C a X')
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (hZ : InComponent C c Z) (hZ' : InComponent C c Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) h)
      (referenceLeftHexagonShort a b c X' Y' Z' hX' hY' hZ').hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree a (b + c) * (i + j + k) + i * (j + k)))
      (reference.data.comp (referenceLeftHexagonShort a b c X Y Z hX hY hZ).hom (reference.data.tensorHom g (reference.data.tensorHom h f))) := by
  have h₁ := isoNaturality_scalar_one L (d := IsoData.assoc C X Y Z)
    (d' := IsoData.assoc C X' Y' Z') (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality f g h)
  have h₂ := referenceExchange_naturality a (b + c) X X' (reference.data.tensorObj Y Z) (reference.data.tensorObj Y' Z')
    hX hX' (hY.tensor referenceProperty hZ) (hY'.tensor referenceProperty hZ')
    f (reference.data.tensorHom g h) i (j + k) hf (referenceProperty.toWeaklyPointedSuperfusionLaws.tensor_grade g h hg hh)
  have h₃ := isoNaturality_scalar_one L (d := IsoData.assoc C Y Z X)
    (d' := IsoData.assoc C Y' Z' X') (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality g h f)
  simpa only [referenceLeftHexagonShort, IsoData.trans, referenceExchangeData, one_mul, mul_one, add_assoc] using
    referenceSignedNaturality_comp _ _ h₁ (referenceSignedNaturality_comp _ _ h₂ h₃)

/-- Signed naturality of the left hexagon long path. -/
theorem referenceLeftHexagonLong_naturality (a b c : ZMod 8) (X X' Y Y' Z Z' : reference.data.Obj)
    (hX : InComponent C a X) (hX' : InComponent C a X')
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (hZ : InComponent C c Z) (hZ' : InComponent C c Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) h)
      (referenceLeftHexagonLong a b c X' Y' Z' hX' hY' hZ').hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree a (b + c) * (i + j + k) + i * (j + k)))
      (reference.data.comp (referenceLeftHexagonLong a b c X Y Z hX hY hZ).hom (reference.data.tensorHom g (reference.data.tensorHom h f))) := by
  have h₁ := referenceExchange_whiskerRight_naturality a b X X' Y Y' Z Z'
    hX hX' hY hY' f g h i j k hf hg hh
  have h₂ := isoNaturality_scalar_one L (d := IsoData.assoc C Y X Z)
    (d' := IsoData.assoc C Y' X' Z') (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality g f h)
  have h₃ := referenceExchange_whiskerLeft_naturality a c Y Y' X X' Z Z'
    hX hX' hZ hZ' g f h j i k hg hf hh
  have he := referenceSignedNaturality_comp _ _ h₁ (referenceSignedNaturality_comp _ _ h₂ h₃)
  have hs : paritySign (ReferenceCommutor.degree a b * (i + j + k) + i * j) *
      (1 * paritySign (ReferenceCommutor.degree a c * (j + i + k) + i * k)) =
      paritySign (ReferenceCommutor.degree a (b + c) * (i + j + k) + i * (j + k)) := by
    simp only [one_mul, ReferenceCommutor.paritySign_pow, ← parity_power_add,
      referenceDegree_add_right]
    congr 2
    ring
  rw [hs] at he
  exact he

/-- Signed naturality of the right hexagon short path. -/
theorem referenceRightHexagonShort_naturality (a b c : ZMod 8) (X X' Y Y' Z Z' : reference.data.Obj)
    (hX : InComponent C a X) (hX' : InComponent C a X')
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (hZ : InComponent C c Z) (hZ' : InComponent C c Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) h)
      (referenceRightHexagonShort a b c X' Y' Z' hX' hY' hZ').hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree (a + b) c * (i + j + k) + (i + j) * k))
      (reference.data.comp (referenceRightHexagonShort a b c X Y Z hX hY hZ).hom (reference.data.tensorHom h (reference.data.tensorHom f g))) := by
  exact referenceExchange_naturality (a + b) c (reference.data.tensorObj X Y) (reference.data.tensorObj X' Y') Z Z'
    (hX.tensor referenceProperty hY) (hX'.tensor referenceProperty hY') hZ hZ'
    (reference.data.tensorHom f g) h (i + j) k (referenceProperty.toWeaklyPointedSuperfusionLaws.tensor_grade f g hf hg) hh

/-- Signed naturality of the right hexagon long path. -/
theorem referenceRightHexagonLong_naturality (a b c : ZMod 8) (X X' Y Y' Z Z' : reference.data.Obj)
    (hX : InComponent C a X) (hX' : InComponent C a X')
    (hY : InComponent C b Y) (hY' : InComponent C b Y')
    (hZ : InComponent C c Z) (hZ' : InComponent C c Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y') (h : reference.data.Hom Z Z') (i j k : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g) (hh : reference.data.IsHomogeneous k h) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) h)
      (referenceRightHexagonLong a b c X' Y' Z' hX' hY' hZ').hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree (a + b) c * (i + j + k) + (i + j) * k))
      (reference.data.comp (referenceRightHexagonLong a b c X Y Z hX hY hZ).hom (reference.data.tensorHom h (reference.data.tensorHom f g))) := by
  have h₁ := isoNaturality_scalar_one L (d := IsoData.assoc C X Y Z)
    (d' := IsoData.assoc C X' Y' Z') (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality f g h)
  have h₂ := referenceExchange_whiskerLeft_naturality b c X X' Y Y' Z Z'
    hY hY' hZ hZ' f g h i j k hf hg hh
  have h₃ := isoNaturality_scalar_one L
    (iso_naturality_symm L (EvenIsoLaws.assoc L X Z Y).toIsoLaws
      (EvenIsoLaws.assoc L X' Z' Y').toIsoLaws (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality f h g))
  have h₄ := referenceExchange_whiskerRight_naturality a c X X' Z Z' Y Y'
    hX hX' hZ hZ' f h g i k j hf hh hg
  have h₅ := isoNaturality_scalar_one L (d := IsoData.assoc C Z X Y)
    (d' := IsoData.assoc C Z' X' Y') (referenceProperty.toWeaklyPointedSuperfusionLaws.associator_naturality h f g)
  have he := referenceSignedNaturality_comp _ _ h₁ (referenceSignedNaturality_comp _ _ h₂
    (referenceSignedNaturality_comp _ _ h₃ (referenceSignedNaturality_comp _ _ h₄ h₅)))
  have hs : 1 * (paritySign (ReferenceCommutor.degree b c * (i + j + k) + j * k) *
      (1 * (paritySign (ReferenceCommutor.degree a c * (i + k + j) + i * k) * 1))) =
      paritySign (ReferenceCommutor.degree (a + b) c * (i + j + k) + (i + j) * k) := by
    simp only [one_mul, mul_one, ReferenceCommutor.paritySign_pow, ← parity_power_add,
      referenceDegree_add_left]
    congr 2
    ring
  rw [hs] at he
  exact he

end RMod.BrundanEllis.Stacking
