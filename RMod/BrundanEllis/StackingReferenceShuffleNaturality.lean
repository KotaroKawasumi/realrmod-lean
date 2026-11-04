import RMod.BrundanEllis.StackingReferenceShuffle
import RMod.BrundanEllis.StackingInterchangeNaturality

/-! Signed naturality of the actual four-factor reference comparison.
The result keeps the parity of the middle exchange and the Koszul sign
from reversing the two middle morphisms. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The actual four-factor shuffle is natural in every homogeneous degree. -/
theorem referenceShuffle_naturality (a b : ZMod 8) (X X' Y Y' Z Z' W W' : reference.data.Obj)
    (hY : InComponent reference.data.toWeaklyPointedSuperfusionData a Y)
    (hY' : InComponent reference.data.toWeaklyPointedSuperfusionData a Y')
    (hZ : InComponent reference.data.toWeaklyPointedSuperfusionData b Z)
    (hZ' : InComponent reference.data.toWeaklyPointedSuperfusionData b Z')
    (f : reference.data.Hom X X') (g : reference.data.Hom Y Y')
    (h : reference.data.Hom Z Z') (k : reference.data.Hom W W') (i j l m : ZMod 2)
    (hf : reference.data.IsHomogeneous i f) (hg : reference.data.IsHomogeneous j g)
    (hh : reference.data.IsHomogeneous l h) (hk : reference.data.IsHomogeneous m k) :
    reference.data.comp (reference.data.tensorHom (reference.data.tensorHom f g) (reference.data.tensorHom h k))
      (referenceShuffleData a b X' Y' Z' W' hY' hZ').hom =
    reference.data.smul (paritySign (ReferenceCommutor.degree a b * (i + j + l + m) + j * l))
      (reference.data.comp (referenceShuffleData a b X Y Z W hY hZ).hom
        (reference.data.tensorHom (reference.data.tensorHom f h) (reference.data.tensorHom g k))) := by
  have hn := referenceExchange_naturality a b Y Y' Z Z' hY hY' hZ hZ' g h j l hg hh
  have ht := interchangeIsoNaturality referenceProperty.toWeaklyPointedSuperfusionLaws f g h k
    (referenceExchangeData a b Y Z hY hZ) (referenceExchangeData a b Y' Z' hY' hZ')
    (ReferenceCommutor.degree a b) i j l m _
    (referenceExchange_grade a b Y Z hY hZ) (referenceExchange_grade a b Y' Z' hY' hZ')
    hf hg hh hk hn
  have hs : ((-1 : ℝ) ^ (ReferenceCommutor.degree a b * i).val *
      paritySign (ReferenceCommutor.degree a b * (j + l) + j * l)) *
        (-1 : ℝ) ^ (m * ReferenceCommutor.degree a b).val =
      paritySign (ReferenceCommutor.degree a b * (i + j + l + m) + j * l) := by
    simp only [ReferenceCommutor.paritySign_pow, ← parity_power_add]
    congr 2
    ring
  rw [hs] at ht
  simpa only [referenceShuffleData] using ht

end RMod.BrundanEllis.Stacking
