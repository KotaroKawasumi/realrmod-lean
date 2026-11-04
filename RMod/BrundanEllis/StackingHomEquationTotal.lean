import RMod.BrundanEllis.Surface
import RMod.Enriched.TotalNaturality

/-! A Hom-object equation evaluated on an arbitrary total vector gives the
corresponding equation of total morphisms on the public declaration surface. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- Evaluate a graded naturality square without requiring monoidal coherence. -/
theorem homEquation_total {D : Type} [SuperCategory D] {H : SuperVec}
    {A B A' B' : Even D}
    (f : H ⟶ SHom D A B) (g : H ⟶ SHom D A' B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ eHomWhiskerLeft SuperVec A b = g ≫ eHomWhiskerRight SuperVec a B')
    (p : ∀ r, H r) :
    tComp D (fun r => f r (p r)) (evenPoint b) =
      tComp D (evenPoint a) (fun r => g r (p r)) := by
  with_unfolding_all
    exact RMod.Regression.hom_equation_total (D := D) f g a b h p

end RMod.BrundanEllis.Stacking
