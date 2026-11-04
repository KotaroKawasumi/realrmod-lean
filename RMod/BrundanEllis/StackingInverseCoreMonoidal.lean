import Mathlib.CategoryTheory.Monoidal.Functor

/-! Keep a chosen inverse and counit when transferring ordinary monoidal coherence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
universe vC vD uC uD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]

/-- Retain the actual chosen inverse and counit of an ordinary equivalence
when giving its inverse the induced monoidal structure. -/
def inverseCoreMonoidal (E : C ≌ D) (M : E.functor.CoreMonoidal) : E.inverse.CoreMonoidal := by
  letI := M.toMonoidal
  letI := E.inverseMonoidal
  exact Functor.CoreMonoidal.ofLaxMonoidal E.inverse

/-- The forward image of the inverse tensorator is specified by the
original tensorator and the retained counit components. -/
theorem inverseCoreMonoidal_tensor_image (E : C ≌ D) (M : E.functor.CoreMonoidal) (X Y : D) :
    (M.μIso (E.inverse.obj X) (E.inverse.obj Y)).hom ≫
      E.functor.map ((inverseCoreMonoidal E M).μIso X Y).hom ≫
      E.counitIso.hom.app (X ⊗ Y) =
    E.counitIso.hom.app X ⊗ₘ E.counitIso.hom.app Y := by
  letI := M.toMonoidal
  letI := E.inverseMonoidal
  change Functor.LaxMonoidal.μ E.functor (E.inverse.obj X) (E.inverse.obj Y) ≫
      E.functor.map (Functor.LaxMonoidal.μ E.inverse X Y) ≫ E.counitIso.hom.app (X ⊗ Y) = _
  rw [E.functor_map_μ_inverse_comp_counitIso_hom_app_tensor,
    Functor.Monoidal.μ_δ_assoc]

end RMod.BrundanEllis.Stacking
