import RMod.Classification.Instances.BiconeToEven

/-! # The same finite total identity proves even universality -/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory CategoryTheory.Limits Superfusion.Category

noncomputable def biconeToEven_isBilimit (C : WeaklyPointedSuperfusion.{0, 0})
    {I : Type} [Fintype I] {V : I → LinearCategory C} (b : Bicone V)
    (hπ : ∀ i, C.data.IsHomogeneous 0 (b.π i)) (hι : ∀ i, C.data.IsHomogeneous 0 (b.ι i))
    (hb : b.IsBilimit) : (biconeToEven C b hπ hι).IsBilimit := by
  apply isBilimitOfTotal
  apply WideSubcategory.hom_ext
  let F := wideSubcategoryInclusion (evenMorphismProperty ℝ (LinearCategory C))
  have hm := F.map_sum (fun i => (biconeToEven C b hπ hι).π i ≫ (biconeToEven C b hπ hι).ι i) Finset.univ
  exact hm.trans (IsBilimit.total hb)

end RMod.Classification
