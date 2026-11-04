import RMod.Hierarchy.Instances.TotalGrading
import RMod.Hierarchy.Instances.EvenLinear

/-!
# The inclusion of the even category into the total category

Evaluation at the even basis vector identifies each even Hom space with
the degree-zero submodule. It preserves composition and linear operations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy
variable (C : Supercategory)

def evenHomGradeEquiv (X Y : C.data.Obj) :
    EHom C.data X Y ≃ₗ[ℝ] grade C X Y 0 where
  toFun f := ⟨evenPoint f, evenPoint_mem_grade C f⟩
  invFun f := homogeneousMap (C.data.Hom X Y) 0 (f.val 0)
  left_inv f := (homogeneousHomEquiv (C.data.Hom X Y) 0).left_inv f
  right_inv f := by
    apply Subtype.ext
    funext b
    by_cases hb : b = 0
    · subst b
      exact homogeneousPoint_map_same (C.data.Hom X Y) 0 (f.val 0)
    · exact (homogeneousPoint_map_ne _ _ _ _ hb).trans (f.property b hb).symm
  map_add' f g := by
    apply Subtype.ext
    funext a
    change evenPoint (f + g) a = evenPoint f a + evenPoint g a
    by_cases h : a = 0
    · subst a
      rfl
    · simp [evenPoint, homogeneousPoint, h]
  map_smul' r f := by
    apply Subtype.ext
    funext a
    change evenPoint (r • f) a = r • evenPoint f a
    by_cases h : a = 0
    · subst a
      rfl
    · simp [evenPoint, homogeneousPoint, h]

def evenToTotal : Even C ⥤ TotalCategory C where
  obj X := totalObj C X
  map f := evenPoint f
  map_id _ := rfl
  map_comp f g := evenPoint_comp C.data f g

instance : (evenToTotal C).Faithful where
  map_injective := fun {X Y} {_ _} h => evenPoint_injective (C.data.Hom X Y) h

instance : (evenToTotal C).Additive where
  map_add {X Y} {f g} := congrArg Subtype.val ((evenHomGradeEquiv C X Y).map_add f g)

instance : (evenToTotal C).Linear ℝ where
  map_smul := fun f r => congrArg Subtype.val ((evenHomGradeEquiv C _ _).map_smul r f)

end RMod.Legacy
