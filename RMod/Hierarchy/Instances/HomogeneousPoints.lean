import RMod.Hierarchy.Instances.TotalComposition

/-!
# Detecting maps from a homogeneous line

A map from a one-dimensional homogeneous line is determined by the image of
its basis vector. In degree zero this identifies the even morphisms with
the degree-zero part of total morphisms.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Category
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.Legacy

theorem homogeneousPoint_injective (V : SuperVec) (a : ZMod 2) :
    Function.Injective (@homogeneousPoint V a) := by
  intro f g h
  funext b
  by_cases hb : b = a
  · subst b
    let e := GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)
    apply (cancel_epi e.inv).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hp := congrFun h a
    simp only [homogeneousPoint] at hp
    have hf : (e.inv ≫ f a) r = r • (e.inv ≫ f a) 1 := by
      simpa using map_smul (e.inv ≫ f a).hom r (1 : ℝ)
    have hg : (e.inv ≫ g a) r = r • (e.inv ≫ g a) 1 := by
      simpa using map_smul (e.inv ≫ g a).hom r (1 : ℝ)
    change (e.inv ≫ f a) r = (e.inv ≫ g a) r
    rw [hf, hg]
    exact congrArg (r • ·) hp
  · exact (GradedObject.isInitialSingleObjApply a (ModuleCat.of ℝ ℝ) b hb).hom_ext _ _

theorem evenPoint_injective (V : SuperVec) : Function.Injective (@evenPoint V) :=
  homogeneousPoint_injective V 0

theorem evenPoint_comp (d : SupercategoryData) {X Y Z : d.Obj}
    (f : EHom d X Y) (g : EHom d Y Z) :
    evenPoint (eComp d f g) = tComp d (evenPoint f) (evenPoint g) := by
  funext a
  rw [tComp_even_left]
  by_cases ha : a = 0
  · subst a
    change ((λ_ (𝟙_ SuperVec)).inv ≫ (f ⊗ₘ g) ≫ d.comp X Y Z) 0
      ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) = _
    have hf := GradedObject.Monoidal.leftUnitor_inv_apply (tensorUnit : SuperVec) 0
    change (GradedObject.Monoidal.leftUnitor (tensorUnit : SuperVec)).inv 0 = _ at hf
    change d.comp X Y Z 0
      (GradedObject.Monoidal.tensorHom f g 0
        ((GradedObject.Monoidal.leftUnitor (tensorUnit : SuperVec)).inv 0
          ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1))) = _
    rw [hf]
    have hfg := ι_tensorHom f g 0 0 0 (zero_add 0)
    have he := congrArg (fun q => q
      (((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1) ⊗ₜ[ℝ]
       ((tensorUnit₀ (I := ZMod 2) (C := ModuleCat ℝ)).inv 1))) hfg
    convert! congrArg (d.comp X Y Z 0) he
  · simp [evenPoint, homogeneousPoint, ha]

end RMod.Legacy
