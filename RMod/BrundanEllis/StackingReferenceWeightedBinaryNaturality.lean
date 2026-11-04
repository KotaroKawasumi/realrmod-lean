import RMod.BrundanEllis.StackingReferenceBinaryNaturality

/-! Coordinate and summand formulas for the actual corrected exterior tensor comparison. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The even binary block has the expected middle interchange sign in every degree. -/
theorem referenceWeightedBinary_even_naturality (a b : ZMod 8)
    (X X' Y Y' Z Z' W W' : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hY' : InComponent reference.data.toWeaklyPointedSuperfusionData a Y')
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z)
    (hZ' : InComponent reference.data.toWeaklyPointedSuperfusionData b Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y')
    (h : reference.data.Hom Z Z') (k : reference.data.Hom W W') (p q : ZMod 2) (β : ℝˣ)
    (hf : reference.data.IsHomogeneous 0 f) (hg : reference.data.IsHomogeneous 0 g)
    (hh : reference.data.IsHomogeneous 0 h) (hk : reference.data.IsHomogeneous 0 k) :
    reference.data.comp
      (reference.data.tensorHom
        (reference.data.tensorHom (reference.data.tensorHom f g) (reference.data.tensorHom h k))
        (reference.data.id (reference.data.pi.factor (p + q + ReferenceCommutor.degree a b))))
      ((referenceBinaryBlockData a b X' Y' Z' W' hY' hZ' p q).scale reference.data.toWeaklyPointedSuperfusionData β).hom =
    reference.data.comp ((referenceBinaryBlockData a b X Y Z W hY hZ p q).scale reference.data.toWeaklyPointedSuperfusionData β).hom
        (reference.data.tensorHom
          (reference.data.tensorHom (reference.data.tensorHom f h) (reference.data.id (reference.data.pi.factor q)))
          (reference.data.tensorHom (reference.data.tensorHom g k) (reference.data.id (reference.data.pi.factor p)))) := by
  let hC := referenceProperty.toWeaklyPointedSuperfusionLaws
  dsimp only [IsoData.scale]
  rw [hC.comp_smul, referenceBinaryBlock_naturality a b X X' Y Y' Z Z' W W'
    hY hY' hZ hZ' f g h k 0 0 0 0 p q hf hg hh hk, hC.smul_comp]
  simp only [zero_mul, show paritySign (0 : ZMod 2) = (1 : ℝ) from rfl, hC.one_smul]

end RMod.BrundanEllis.Stacking
