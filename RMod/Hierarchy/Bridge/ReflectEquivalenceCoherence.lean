import RMod.Hierarchy.Bridge.ReflectEquivalenceData

/-!
# Reflection of the even monoidal coherence equations

The even Hom equivalence preserves composition, tensor products, and the
structural maps, so the three new coherence equations imply the old ones.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy.Hierarchy
variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  (E : MonoidalSuperequivalence (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D))

theorem reflect_associativity (X Y Z : C.data.Obj) :
    D.data.comp (D.data.comp (D.data.tensorHom ((reflectMonoidalFunctorData E).tensorHom X Y)
      (D.data.id (E.data.forward.obj Z))) ((reflectMonoidalFunctorData E).tensorHom (C.data.tensorObj X Y) Z))
      ((reflectMonoidalFunctorData E).map (C.data.associatorHom X Y Z)) =
    D.data.comp (D.data.comp (D.data.associatorHom (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z))
      (D.data.tensorHom (D.data.id (E.data.forward.obj X)) ((reflectMonoidalFunctorData E).tensorHom Y Z)))
      ((reflectMonoidalFunctorData E).tensorHom X (C.data.tensorObj Y Z)) := by
  let X₀ : Even (ofOldSupercategory C) := X
  let Y₀ : Even (ofOldSupercategory C) := Y
  let Z₀ : Even (ofOldSupercategory C) := Z
  let FX : Even (ofOldSupercategory D) := E.evenForward.obj X₀
  let FY : Even (ofOldSupercategory D) := E.evenForward.obj Y₀
  let FZ : Even (ofOldSupercategory D) := E.evenForward.obj Z₀
  let μ₁ := (E.data.tensorIso X₀ Y₀).hom
  let μ₂ := (E.data.tensorIso (X₀ ⊗ Y₀) Z₀).hom
  let μ₃ := (E.data.tensorIso Y₀ Z₀).hom
  let μ₄ := (E.data.tensorIso X₀ (Y₀ ⊗ Z₀)).hom
  let a := E.evenForward.map (α_ X₀ Y₀ Z₀).hom
  have h := congrArg (oldValue D) (E.laws.associativity X₀ Y₀ Z₀)
  change oldValue D ((μ₁ ▷ FZ) ≫ μ₂ ≫ a) = oldValue D ((α_ FX FY FZ).hom ≫ (FX ◁ μ₃) ≫ μ₄) at h
  erw [oldValue_comp D (μ₁ ▷ FZ) (μ₂ ≫ a), oldValue_comp D μ₂ a,
    oldValue_comp D (α_ FX FY FZ).hom ((FX ◁ μ₃) ≫ μ₄), oldValue_comp D (FX ◁ μ₃) μ₄,
    oldValue_whiskerRight D μ₁ FZ, oldValue_whiskerLeft D FX μ₃,
    oldValue_associator D FX FY FZ,
    ← reflectSuperfunctor_even E.forward (α_ X₀ Y₀ Z₀).hom,
    oldValue_associator C X₀ Y₀ Z₀] at h
  simp only [D.laws.comp_assoc]
  exact h

theorem reflect_left_unit (X : C.data.Obj) :
    D.data.comp (D.data.comp (D.data.tensorHom (reflectMonoidalFunctorData E).unitHom
      (D.data.id (E.data.forward.obj X))) ((reflectMonoidalFunctorData E).tensorHom C.data.tensorUnit X))
      ((reflectMonoidalFunctorData E).map (C.data.leftUnitorHom X)) = D.data.leftUnitorHom (E.data.forward.obj X) := by
  let X₀ : Even (ofOldSupercategory C) := X
  let FX : Even (ofOldSupercategory D) := E.evenForward.obj X₀
  let u := E.data.unitIso.hom
  let μ := (E.data.tensorIso (𝟙_ (Even (ofOldSupercategory C))) X₀).hom
  let a := E.evenForward.map (λ_ X₀).hom
  have h := congrArg (oldValue D) (E.laws.left_unit X₀)
  change oldValue D ((u ▷ FX) ≫ μ ≫ a) = oldValue D (λ_ FX).hom at h
  erw [oldValue_comp D (u ▷ FX) (μ ≫ a), oldValue_comp D μ a,
    oldValue_whiskerRight D u FX, oldValue_leftUnitor D FX,
    ← reflectSuperfunctor_even E.forward (λ_ X₀).hom, oldValue_leftUnitor C X₀] at h
  simp only [D.laws.comp_assoc]
  exact h

theorem reflect_right_unit (X : C.data.Obj) :
    D.data.comp (D.data.comp (D.data.tensorHom (D.data.id (E.data.forward.obj X))
      (reflectMonoidalFunctorData E).unitHom) ((reflectMonoidalFunctorData E).tensorHom X C.data.tensorUnit))
      ((reflectMonoidalFunctorData E).map (C.data.rightUnitorHom X)) = D.data.rightUnitorHom (E.data.forward.obj X) := by
  let X₀ : Even (ofOldSupercategory C) := X
  let FX : Even (ofOldSupercategory D) := E.evenForward.obj X₀
  let u := E.data.unitIso.hom
  let μ := (E.data.tensorIso X₀ (𝟙_ (Even (ofOldSupercategory C)))).hom
  let a := E.evenForward.map (ρ_ X₀).hom
  have h := congrArg (oldValue D) (E.laws.right_unit X₀)
  change oldValue D ((FX ◁ u) ≫ μ ≫ a) = oldValue D (ρ_ FX).hom at h
  erw [oldValue_comp D (FX ◁ u) (μ ≫ a), oldValue_comp D μ a,
    oldValue_whiskerLeft D FX u, oldValue_rightUnitor D FX,
    ← reflectSuperfunctor_even E.forward (ρ_ X₀).hom, oldValue_rightUnitor C X₀] at h
  simp only [D.laws.comp_assoc]
  exact h

end RMod.Legacy.Hierarchy
