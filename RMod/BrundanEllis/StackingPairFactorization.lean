import RMod.BrundanEllis.StackingProductStructure

/-! The even part of an enriched pairing commutes with postcomposition.
In particular, the completion pairing is the raw ordinary pairing followed
by the enriched embedding on even categories. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
variable {A B C D : Type} [SuperCategory A] [SuperCategory B]
  [SuperCategory C] [SuperCategory D]

theorem pair_comp (F : SuperFunctor (SuperTensorProduct A B) C) (G : SuperFunctor C D) :
    evenPairFunctor (F.comp SuperVec G) = evenPairFunctor F ⋙ G.forget := by
  apply CategoryTheory.Functor.ext (h_obj := fun _ => rfl)

theorem pair_product_factorization (F : SuperFunctor (SuperTensorProduct A B) D) :
    evenPairFunctor F = productPair A B ⋙ F.forget := by
  apply CategoryTheory.Functor.ext (h_obj := fun _ => rfl)

end RMod.BrundanEllis.Stacking
