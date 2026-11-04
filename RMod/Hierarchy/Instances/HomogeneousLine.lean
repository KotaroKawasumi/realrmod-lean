import RMod.Hierarchy.Instances.HomogeneousPoints

/-!
# Maps from homogeneous lines

The chosen basis vector of a homogeneous real line represents every vector
of the corresponding degree. The construction is inverse to evaluation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.Legacy

def homogeneousLine (a : ZMod 2) : SuperVec :=
  (GradedObject.single a).obj (ModuleCat.of ℝ ℝ)

def homogeneousMap (V : SuperVec) (a : ZMod 2) (v : V a) :
    homogeneousLine a ⟶ V := fun b =>
  if h : b = a then
    (GradedObject.singleObjApplyIsoOfEq a (ModuleCat.of ℝ ℝ) b h).hom ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ (h.symm ▸ v))
  else (GradedObject.isInitialSingleObjApply a (ModuleCat.of ℝ ℝ) b h).to _

@[simp]
theorem homogeneousPoint_map_same (V : SuperVec) (a : ZMod 2) (v : V a) :
    homogeneousPoint a (homogeneousMap V a v) a = v := by
  simp only [homogeneousPoint, homogeneousMap]
  let e := GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)
  change ((e.inv ≫ e.hom ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _ v)) 1) = v
  rw [Iso.inv_hom_id_assoc]
  exact one_smul ℝ v

@[simp]
theorem homogeneousPoint_map_ne (V : SuperVec) (a b : ZMod 2) (v : V a) (h : b ≠ a) :
    homogeneousPoint a (homogeneousMap V a v) b = 0 := by
  simp [homogeneousPoint, h]

/-- Evaluation gives a linear equivalence with the degree-a component. -/
def homogeneousHomEquiv (V : SuperVec) (a : ZMod 2) :
    (homogeneousLine a ⟶ V) ≃ₗ[ℝ] V a where
  toFun f := homogeneousPoint a f a
  invFun := homogeneousMap V a
  left_inv f := by
    apply homogeneousPoint_injective V a
    funext b
    by_cases h : b = a
    · subst b
      exact homogeneousPoint_map_same V a _
    · simp [homogeneousPoint, h]
  right_inv := homogeneousPoint_map_same V a
  map_add' f g := by
    simp only [homogeneousPoint]
    change (f a + g a) ((GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)).inv 1) = _
    rfl
  map_smul' r f := by
    simp only [homogeneousPoint]
    change (r • f a) ((GradedObject.singleObjApplyIso a (ModuleCat.of ℝ ℝ)).inv 1) = _
    rfl

end RMod.Legacy
