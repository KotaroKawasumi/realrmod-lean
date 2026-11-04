import RMod.BrundanEllis.StackingReferenceBinaryBlock
import RMod.BrundanEllis.StackingReferenceShuffleNaturality
import RMod.BrundanEllis.StackingParityRedistributionNaturality

/-! Naturality of the even binary comparison.  Parity redistribution
cancels the degree of the reference exchange, leaving exactly the Koszul
sign from interchanging the two middle morphisms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The even binary block has the expected middle interchange sign in every degree. -/
theorem referenceBinaryBlock_naturality (a b : ZMod 8)
    (X X' Y Y' Z Z' W W' : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hY' : InComponent reference.data.toWeaklyPointedSuperfusionData a Y')
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z)
    (hZ' : InComponent reference.data.toWeaklyPointedSuperfusionData b Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y')
    (h : reference.data.Hom Z Z') (k : reference.data.Hom W W') (i j l m p q : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g)
    (hh : reference.data.IsHomogeneous l h) (hk : reference.data.IsHomogeneous m k) :
    reference.data.comp
      (reference.data.tensorHom
        (reference.data.tensorHom (reference.data.tensorHom f g) (reference.data.tensorHom h k))
        (reference.data.id (reference.data.pi.factor (p + q + ReferenceCommutor.degree a b))))
      (referenceBinaryBlockData a b X' Y' Z' W' hY' hZ' p q).hom =
    reference.data.smul (paritySign (j * l))
      (reference.data.comp (referenceBinaryBlockData a b X Y Z W hY hZ p q).hom
        (reference.data.tensorHom
          (reference.data.tensorHom (reference.data.tensorHom f h) (reference.data.id (reference.data.pi.factor q)))
          (reference.data.tensorHom (reference.data.tensorHom g k) (reference.data.id (reference.data.pi.factor p))))) := by
  let C := reference.data.toWeaklyPointedSuperfusionData
  have hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  have htotal : C.IsHomogeneous ((i + l) + (j + m)) (C.tensorHom (C.tensorHom f g) (C.tensorHom h k)) := by
    rw [show (i + l) + (j + m) = (i + j) + (l + m) by ring]
    exact hC.tensor_grade _ _ (hC.tensor_grade _ _ hf hg) (hC.tensor_grade _ _ hh hk)
  have hn := referenceShuffle_naturality a b X X' Y Y' Z Z' W W' hY hY' hZ hZ' f g h k i j l m hf hg hh hk
  have ht := parityRedistribution_naturality hC referenceProperty.pi p q (ReferenceCommutor.degree a b)
    (i + l) (j + m) (referenceShuffleData a b X Y Z W hY hZ)
    (referenceShuffleData a b X' Y' Z' W' hY' hZ') _ _ _ htotal
    (hC.tensor_grade _ _ hf hh) (hC.tensor_grade _ _ hg hk) _ hn
  have hs : (-1 : ℝ) ^ (ReferenceCommutor.degree a b * ((i + l) + (j + m))).val *
      paritySign (ReferenceCommutor.degree a b * (i + j + l + m) + j * l) = paritySign (j * l) := by
    simp only [ReferenceCommutor.paritySign_pow, ← parity_power_add]
    congr 2
    ring_nf
    simp [CharTwo.two_eq_zero]
  rw [hs] at ht
  exact ht

end RMod.BrundanEllis.Stacking
