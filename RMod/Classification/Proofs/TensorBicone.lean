import RMod.Classification.Instances.TensorBicone
import RMod.Classification.Instances.TensorHomBilinear

/-! # Bilinearity proves the total identity of the tensor presentation -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I J : Type} [Fintype I] [Fintype J]
  {V : I → LinearCategory C} {W : J → LinearCategory C}

noncomputable def tensorBicone_isBilimit (b : Bicone V) (c : Bicone W)
    (hbι : ∀ i, C.data.IsHomogeneous 0 (b.ι i)) (hbπ : ∀ i, C.data.IsHomogeneous 0 (b.π i))
    (hb : b.IsBilimit) (hc : c.IsBilimit) : (tensorBicone C b c hbι).IsBilimit := by
  apply isBilimitOfTotal
  change (∑ ij : I × J, (show @Quiver.Hom (LinearCategory C) _
    (C.data.tensorObj b.pt c.pt) (C.data.tensorObj b.pt c.pt) from
      C.data.comp (C.data.tensorHom (b.π ij.1) (c.π ij.2))
        (C.data.tensorHom (b.ι ij.1) (c.ι ij.2)))) = C.data.id (C.data.tensorObj b.pt c.pt)
  rw [Fintype.sum_prod_type]
  simp_rw [interchange_first_even C.laws _ _ _ _ (hbπ _)]
  let T := tensorHomBilinear C b.pt b.pt c.pt c.pt
  change (∑ i, ∑ j, T (b.π i ≫ b.ι i) (c.π j ≫ c.ι j)) = _
  simp_rw [← map_sum]
  rw [IsBilimit.total hc]
  change (∑ i, T.flip (𝟙 c.pt) (b.π i ≫ b.ι i)) = _
  rw [← map_sum, IsBilimit.total hb]
  exact C.laws.tensor_id _ _

end RMod.Classification
