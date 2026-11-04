import RMod.Classification.Instances.ReconstructionMappedTensorBicone

/-! # Identifying the product-component output with its fixed degree -/

set_option autoImplicit false

namespace RMod.Classification

theorem reconstructionTensorOutputRealization_obj (A C : PiSuperfusion.{0, 0})
    (hC : ReferenceProperty C.data) (X Y : LinearCategory A.toWeaklyPointedSuperfusion)
    (k g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    (reconstructionComponentRealization A C hC k).obj (reconstructionTensorOutputSpan A X Y k g) =
      (reconstructionComponentRealization A C hC (g * (g⁻¹ * k))).obj
        (reconstructionTensorSpanObject A X Y g (g⁻¹ * k)) := by
  generalize he : g⁻¹ * k = h
  have hk : g * h = k := by rw [← he, mul_inv_cancel_left]
  subst k
  apply congrArg (reconstructionComponentRealization A C hC (g * h)).obj
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  exact congrArg (A.data.tensorObj ((reconstructionSourceEquivalence A).inverse.obj X g).obj)
    (congrArg (fun q => ((reconstructionSourceEquivalence A).inverse.obj Y q).obj) he)

end RMod.Classification
