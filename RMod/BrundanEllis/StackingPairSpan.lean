import RMod.BrundanEllis.StackingBilinear
import RMod.BrundanEllis.StackingFiniteSpan
import RMod.BrundanEllis.StackingProductEven

/-! An enriched pairing is additive separately in its two variables.
Consequently, finite spans in the factors map into the finite span of
paired generators, even before fusion properties of the target are known. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace RMod.BrundanEllis.Stacking

instance superFunctorAdditive {C D : Type} [SuperCategory C] [SuperCategory D]
    (F : SuperFunctor C D) : F.forget.Additive where
  map_add {X Y} f g := by
    apply funext
    intro a
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => map_add (F.map X Y a).hom (f a x) (g a x))

namespace FiniteSpan
variable {C D : Type} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] {I J : Type} {Z : I → C} {W : J → D}

theorem map (F : C ⥤ D) [F.Additive]
    (h : ∀ i, FiniteSpan W (F.obj (Z i))) {X : C} (hX : FiniteSpan Z X) :
    FiniteSpan W (F.obj X) := by
  obtain ⟨n, i, ⟨e⟩⟩ := hX
  exact of_iso (F.mapIso e ≪≫ F.mapBiproduct _) (finite_biproduct _ (fun j => h (i j)))

end FiniteSpan

variable {A B D : Type} [SuperCategory A] [SuperCategory B] [SuperCategory D]
  [HasFiniteBiproducts (Even A)] [HasFiniteBiproducts (Even B)]
  [HasFiniteBiproducts (Even D)]

/-- Separate additivity extends a pairing from its generators to their finite spans. -/
theorem pair_span (F : SuperFunctor (SuperTensorProduct A B) D)
    {I J K : Type} (Z : I → Even A) (W : J → Even B) (U : K → Even D)
    (h : ∀ i j, FiniteSpan U ((evenPairFunctor F).obj (Z i, W j)))
    {X : Even A} {Y : Even B} (hX : FiniteSpan Z X) (hY : FiniteSpan W Y) :
    FiniteSpan U ((evenPairFunctor F).obj (X, Y)) := by
  apply FiniteSpan.map ((insertRight SuperVec (ForgetEnrichment.to SuperVec Y)).comp SuperVec F).forget
    (fun i => ?_) hX
  exact FiniteSpan.map
    ((insertLeft SuperVec (ForgetEnrichment.to SuperVec (Z i))).comp SuperVec F).forget
    (h i) hY

end RMod.BrundanEllis.Stacking
