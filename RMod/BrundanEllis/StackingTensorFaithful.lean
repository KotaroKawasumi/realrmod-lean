import RMod.BrundanEllis.StackingFaithfulForget

/-! Tensoring and composing superfunctors preserve full faithfulness in
every degree. The tensor case uses the tensor of the actual Hom-object
isomorphisms, so it includes the mixed parity summands. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

theorem iso_component_bijective {V W : SuperVec} (e : V ≅ W) (a : ZMod 2) :
    Function.Bijective (e.hom a) := by
  have hleft : Function.LeftInverse (e.inv a) (e.hom a) :=
    fun x => congrArg (fun f => f a x) e.hom_inv_id
  have hright : Function.RightInverse (e.inv a) (e.hom a) :=
    fun x => congrArg (fun f => f a x) e.inv_hom_id
  exact ⟨hleft.injective, hright.surjective⟩

variable {A B C D E : Type} [SuperCategory A] [SuperCategory B]
  [SuperCategory C] [SuperCategory D] [SuperCategory E]

theorem tensor_functors_bijective (F : SuperFunctor A C) (G : SuperFunctor B D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (hG : ∀ X Y a, Function.Bijective (G.map X Y a))
    (X Y : SuperTensorProduct A B) (a : ZMod 2) :
    Function.Bijective ((RMod.tensorEnrichedFunctors SuperVec F G).map X Y a) :=
  iso_component_bijective (superHomIso F hF X.1 Y.1 ⊗ᵢ superHomIso G hG X.2 Y.2) a

theorem comp_functors_bijective (F : SuperFunctor A B) (G : SuperFunctor B C)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (hG : ∀ X Y a, Function.Bijective (G.map X Y a))
    (X Y : A) (a : ZMod 2) :
    Function.Bijective ((F.comp SuperVec G).map X Y a) :=
  (hG (F.obj X) (F.obj Y) a).comp (hF X Y a)

end RMod.BrundanEllis.Stacking
