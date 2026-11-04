import RMod.Hierarchy.Abstract.Superfunctor
import RMod.Hierarchy.Instances.TotalGrading
import RMod.Hierarchy.Instances.GradedTensorPoints

/-!
# The total linear functor of an enriched superfunctor

An enriched map acts degree by degree. Its enriched identity and
composition equations therefore give the ordinary total functor laws,
while the linear Hom maps preserve the grading and scalar operations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace RMod.Legacy
variable {C D : Supercategory} (F : Superfunctor C D)

theorem tMap_add {X Y : C.data.Obj} (f g : THom C.data X Y) :
    tMap F.data (f + g) = tMap F.data f + tMap F.data g := by
  funext a
  exact map_add (F.data.map X Y a).hom (f a) (g a)

theorem tMap_smul {X Y : C.data.Obj} (r : ℝ) (f : THom C.data X Y) :
    tMap F.data (r • f) = r • tMap F.data f := by
  funext a
  exact map_smul (F.data.map X Y a).hom r (f a)

theorem tMap_zero (X Y : C.data.Obj) : tMap F.data (0 : THom C.data X Y) = 0 := by
  funext a
  exact map_zero (F.data.map X Y a).hom

theorem tMap_mem_grade {X Y : C.data.Obj} {a : ZMod 2} (f : THom C.data X Y)
    (hf : f ∈ grade C X Y a) : tMap F.data f ∈ grade D (F.data.obj X) (F.data.obj Y) a := by
  intro b hb
  change F.data.map X Y b (f b) = 0
  rw [hf b hb, map_zero]

theorem tMap_evenPoint {X Y : C.data.Obj} (f : EHom C.data X Y) :
    tMap F.data (evenPoint f) = evenPoint (f ≫ F.data.map X Y) := by
  funext a
  by_cases ha : a = 0
  · subst a
    rfl
  · change F.data.map X Y a (evenPoint f a) = evenPoint (f ≫ F.data.map X Y) a
    simp [evenPoint, homogeneousPoint, ha]

theorem tMap_id (X : C.data.Obj) :
    tMap F.data (evenPoint (C.data.id X)) = evenPoint (D.data.id (F.data.obj X)) := by
  rw [tMap_evenPoint, F.laws.map_id]

theorem tMap_comp {X Y Z : C.data.Obj} (f : THom C.data X Y) (g : THom C.data Y Z) :
    tMap F.data (tComp C.data f g) = tComp D.data (tMap F.data f) (tMap F.data g) := by
  funext a
  simp only [tMap, tComp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg (fun m => m a
    (gradedTmul (C.data.Hom X Y) (C.data.Hom Y Z) i (a - i) a (by abel) (f i) (g (a - i))))
    (F.laws.map_comp X Y Z)
  change F.data.map X Z a (C.data.comp X Y Z a _) =
    D.data.comp (F.data.obj X) (F.data.obj Y) (F.data.obj Z) a
      ((F.data.map X Y ⊗ₘ F.data.map Y Z) a _) at he
  erw [tensorHom_gradedTmul] at he
  exact he

end RMod.Legacy
