import RMod.BrundanEllis.StackingFunctorPi
import RMod.Hierarchy.Instances.EvenTotal

/-! Even isomorphisms and homogeneous composition act on parity orbits
without any fusion hypotheses. This allows orbit finiteness to be transported
while constructing the fusion structure itself. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable (C : Type) [SuperCategory C]

/-- Forget the degree-zero restriction on an ordinary even arrow. -/
def superEvenToTotal : Even C ⥤ TotalCategory C where
  obj X := ForgetEnrichment.to SuperVec X
  map f := evenPoint (ForgetEnrichment.homTo SuperVec f)
  map_id X := rfl
  map_comp f g := by
    with_unfolding_all
      exact RMod.Legacy.evenPoint_comp (RMod.StatementLegacy.toLegacySupercategory (Bridge.bundled C)).data f g

theorem even_point_grade {X Y : Even C} (f : X ⟶ Y) :
    (superEvenToTotal C).map f ∈ grade C X Y 0 := by
  intro b hb
  change b ≠ 0 at hb
  change homogeneousPoint 0 (ForgetEnrichment.homTo SuperVec f) b = 0
  simp only [homogeneousPoint, dif_neg hb]

theorem even_iso_orbit {X Y : Even C} (e : X ≅ Y) : SameParityOrbit C X Y :=
  ⟨0, (superEvenToTotal C).mapIso e, even_point_grade C e.hom, even_point_grade C e.inv⟩

theorem homogeneous_comp_grade {X Y Z : C} {a b : ZMod 2}
    {f : THom C X Y} {g : THom C Y Z}
    (hf : f ∈ grade C X Y a) (hg : g ∈ grade C Y Z b) :
    tComp C f g ∈ grade C X Z (a + b) := by
  with_unfolding_all
    exact RMod.Legacy.tComp_mem_grade
      (RMod.StatementLegacy.toLegacySupercategory (Bridge.bundled C)) f g hf hg

theorem parity_orbit_trans {X Y Z : C} (h : SameParityOrbit C X Y)
    (k : SameParityOrbit C Y Z) : SameParityOrbit C X Z := by
  obtain ⟨a, e, he, hi⟩ := h
  obtain ⟨b, f, hf, hj⟩ := k
  refine ⟨a + b, e ≪≫ f, homogeneous_comp_grade C he hf, ?_⟩
  change tComp C f.inv e.inv ∈ grade C Z X (a + b)
  rw [add_comm a b]
  exact homogeneous_comp_grade C hj hi

end RMod.BrundanEllis.Stacking
