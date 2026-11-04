import RMod.BrundanEllis.StackingDeligne
import RMod.BrundanEllis.StackingDiagonalInclusion

/-! Stacking is the finite additive, parity and even-retract completion
of the same-label diagonal inside the constructed Deligne product. The
only label comparison is transport along the supplied group equality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis
namespace Stacking

def groupEqualityMulEquiv {G H : FiniteGrp.{0}} (h : G = H) : G ≃* H where
  toFun g := h ▸ g
  invFun g := h.symm ▸ g
  left_inv := by cases h; intro g; rfl
  right_inv := by cases h; intro g; rfl
  map_mul' := by cases h; intro g k; rfl

theorem groupEqualityMulEquiv_apply {G H : FiniteGrp.{0}} (h : G = H) (g : G) :
    groupEqualityMulEquiv h g = h ▸ g := by
  cases h
  rfl

end Stacking
open Stacking

def stack (s t : Twist) (h : s.group = t.group) : WeaklyPointedFusionPiSuperCat :=
  diagonalCompletion s t (groupEqualityMulEquiv h) (deligne (pullback s) (pullback t))
    (delignePairing (pullback s) (pullback t)) (deligneMonoidal (pullback s) (pullback t))

def stackInclusion (s t : Twist) (h : s.group = t.group) :
    SuperFunctor (stack s t h) (deligne (pullback s) (pullback t)) :=
  diagonalInclusion s t (groupEqualityMulEquiv h) (deligne (pullback s) (pullback t))
    (delignePairing (pullback s) (pullback t)) (deligneMonoidal (pullback s) (pullback t))

def stackMonoidal (s t : Twist) (h : s.group = t.group) :
    (stackInclusion s t h).forget.CoreMonoidal :=
  diagonalInclusionMonoidal s t (groupEqualityMulEquiv h) (deligne (pullback s) (pullback t))
    (delignePairing (pullback s) (pullback t)) (deligneMonoidal (pullback s) (pullback t))

-- Keep the large completed-category bundles abstract during type comparison.
attribute [local irreducible] deligne stack stackInclusion stackMonoidal

/-- The full monoidal inclusion has exactly the prescribed diagonal hull as its image. -/
theorem stack_data (s t : Twist) (h : s.group = t.group) :
    let C := stack s t h
    let D := deligne (pullback s) (pullback t)
    let F := stackInclusion s t h
    let M := stackMonoidal s t h
    (∀ X Y a, Function.Bijective (F.map X Y a)) ∧
    (∀ {X X' Y Y'} (f : THom C X X') (g : THom C Y Y'),
      tComp D (tTensor (C := D) (MonoidalSuperCategory.tensor (C := D)) MonoidalSuperCategory.tensor_objects
        (tMap F f) (tMap F g)) (evenPoint (M.μIso X' Y').hom) =
      tComp D (evenPoint (M.μIso X Y).hom)
        (tMap F (tTensor (C := C) (MonoidalSuperCategory.tensor (C := C))
          MonoidalSuperCategory.tensor_objects f g))) ∧
    (∀ Z : Even D,
      (∃ X : Even C, Nonempty (F.forget.obj X ≅ Z)) ↔
      AddPiHull D (fun g : s.group => evenObj D
        ((delignePairing (pullback s) (pullback t)).obj
          (pullbackSimple s g, pullbackSimple t (h ▸ g)))) Z)  := by
  unfold stack stackInclusion stackMonoidal
  apply diagonalCompletion_data

end RMod.BrundanEllis
