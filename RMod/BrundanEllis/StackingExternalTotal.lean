import RMod.BrundanEllis.StackingExternalObjects
import RMod.BrundanEllis.StackingTensorHomDimension
import RMod.BrundanEllis.StackingTensorPi
import Superfusion.Bimod.GradedModule

/-! The exterior map on total Hom spaces is the tensor distribution over
finite coordinate families followed by the actual reference tensor maps.
Every coordinate stays in its prescribed Brauer--Wall component. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open CategoryTheory
open scoped TensorProduct
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Keep the reference category visible to typeclass search in coordinate families. -/
@[implicit_reducible] def referenceHom (X Y : reference.data.Obj) : Type :=
  reference.data.Hom X Y

instance referenceHomAddCommGroup (X Y : reference.data.Obj) : AddCommGroup (referenceHom X Y) :=
  (LinearCategory.preadditive reference.toWeaklyPointedSuperfusion).homGroup X Y

instance referenceHomModule (X Y : reference.data.Obj) : Module ℝ (referenceHom X Y) :=
  (LinearCategory.linear reference.toWeaklyPointedSuperfusion).homModule X Y

/-- The two presentations have identical coordinatewise linear operations. -/
def pullbackHomCoordinates (s : Twist) (X Y : pullback s) :
    (@Quiver.Hom (LinearCategory (oldPullback s).toWeaklyPointedSuperfusion) _ X Y) ≃ₗ[ℝ]
      (∀ g : s.group, referenceHom (X g).val (Y g).val) where
  toFun f g := f g
  invFun f g := f g
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The tensor Hom map at a fixed pair of support labels is an isomorphism. -/
def exteriorCoordinateEquiv (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g : s.group) (h : t.group) :
    ((referenceHom (X g).val (X' g).val) ⊗[ℝ]
      (referenceHom (Y h).val (Y' h).val)) ≃ₗ[ℝ]
      (referenceHom
        (exteriorObject s t X Y (g, h)).val (exteriorObject s t X' Y' (g, h)).val) :=
  LinearEquiv.ofBijective (Raw.tensorHomLinear reference.toWeaklyPointedSuperfusion _ _ _ _)
    (Raw.tensorHomLinear_bijective_in_components reference referenceProperty
      (X g).property (X' g).property (Y h).property (Y' h).property)

/-- Assemble the coordinate isomorphisms, retaining the actual tensor formula. -/
def exteriorTotalEquiv (s t : Twist) (X X' : pullback s) (Y Y' : pullback t) :
    ((@Quiver.Hom (LinearCategory (oldPullback s).toWeaklyPointedSuperfusion) _ X X') ⊗[ℝ]
      (@Quiver.Hom (LinearCategory (oldPullback t).toWeaklyPointedSuperfusion) _ Y Y')) ≃ₗ[ℝ]
      (@Quiver.Hom (LinearCategory (oldPullback (exteriorTwist s t).val).toWeaklyPointedSuperfusion) _
        (exteriorObject s t X Y) (exteriorObject s t X' Y')) := by
  letI := Fintype.ofFinite s.group
  letI := Fintype.ofFinite t.group
  exact (TensorProduct.congr (pullbackHomCoordinates s X X') (pullbackHomCoordinates t Y Y')).trans
    ((Linear.tensorPiEquiv _ _).trans
      ((LinearEquiv.piCongrRight fun gh : s.group × t.group =>
        exteriorCoordinateEquiv s t X X' Y Y' gh.1 gh.2).trans
          (pullbackHomCoordinates (exteriorTwist s t).val _ _).symm))

theorem exteriorTotalEquiv_tmul (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (f : @Quiver.Hom (LinearCategory (oldPullback s).toWeaklyPointedSuperfusion) _ X X')
    (q : @Quiver.Hom (LinearCategory (oldPullback t).toWeaklyPointedSuperfusion) _ Y Y')
    (gh : s.group × t.group) :
    exteriorTotalEquiv s t X X' Y Y' (f ⊗ₜ[ℝ] q) gh = reference.data.tensorHom (f gh.1) (q gh.2) := by
  letI := Fintype.ofFinite s.group
  letI := Fintype.ofFinite t.group
  simp only [exteriorTotalEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul]
  change Raw.tensorHomLinear reference.toWeaklyPointedSuperfusion
    (X gh.1).val (X' gh.1).val (Y gh.2).val (Y' gh.2).val
    (Linear.tensorPiEquiv (fun g : s.group => referenceHom (X g).val (X' g).val)
      (fun h : t.group => referenceHom (Y h).val (Y' h).val)
      ((pullbackHomCoordinates s X X' f) ⊗ₜ[ℝ] (pullbackHomCoordinates t Y Y' q)) gh) = _
  rw [Linear.tensorPiEquiv_tmul]
  rfl

/-- The total exterior isomorphism preserves homogeneous degrees. -/
theorem exteriorTotalEquiv_grade (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    {a : ZMod 2}
    {z : (@Quiver.Hom (LinearCategory (oldPullback s).toWeaklyPointedSuperfusion) _ X X') ⊗[ℝ]
      (@Quiver.Hom (LinearCategory (oldPullback t).toWeaklyPointedSuperfusion) _ Y Y')}
    (hz : z ∈ Superfusion.Bimod.tensorGrading
      (LinearCategory.grade (oldPullback s).toWeaklyPointedSuperfusion X X')
      (LinearCategory.grade (oldPullback t).toWeaklyPointedSuperfusion Y Y') a) :
    exteriorTotalEquiv s t X X' Y Y' z ∈
      LinearCategory.grade (oldPullback (exteriorTwist s t).val).toWeaklyPointedSuperfusion
        (exteriorObject s t X Y) (exteriorObject s t X' Y') a := by
  refine Superfusion.Bimod.tensorGrading_induction _ _
    (motive := fun z => exteriorTotalEquiv s t X X' Y Y' z ∈
      LinearCategory.grade (oldPullback (exteriorTwist s t).val).toWeaklyPointedSuperfusion
        (exteriorObject s t X Y) (exteriorObject s t X' Y') a) hz ?_ ?_ ?_ ?_
  · intro i j f q hij hf hq
    subst a
    intro gh
    rw [exteriorTotalEquiv_tmul]
    exact reference.laws.tensor_grade _ _ (hf gh.1) (hq gh.2)
  · simp
  · intro x y hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro r x hx
    simpa using Submodule.smul_mem _ r hx

end RMod.BrundanEllis.Stacking
