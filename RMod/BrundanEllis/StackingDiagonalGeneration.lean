import RMod.BrundanEllis.StackingDiagonalRestriction
import RMod.BrundanEllis.StackingImageGeneration

/-! Each group label occurs in the restricted image of a diagonal generator.
Its nonzero simple retract, together with parity and finite sums, generates
the whole target and gives essential surjectivity of the actual functor. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- The same-label tensor is an object of the prescribed stack. -/
def stackGenerator (s t : Twist) (h : s.group = t.group) (g : s.group) : stack s t h :=
  hullGenerator (deligne (pullback s) (pullback t))
    (diagonalGenerator s t (groupEqualityMulEquiv h) (deligne (pullback s) (pullback t))
      (delignePairing (pullback s) (pullback t))) g

/-- A diagonal generator evaluated in the restricted external model. -/
def restrictedDiagonalGenerator (s t : Twist) (h : s.group = t.group) (g : s.group) :
    Even (pullback (diagonalRestrictedTwist s t h).val) :=
  (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)).forget.obj
    (evenObj _ ((reversedExteriorPairing s t).obj
      (pullbackSimple s g, pullbackSimple t (h ▸ g))))

/-- Completion and restriction retain the actual generator comparison. -/
def stackRestrictionGeneratorIso (s t : Twist) (h : s.group = t.group) (g : s.group) :
    (stackRestriction s t h).forget.obj (evenObj _ (stackGenerator s t h g)) ≅
      restrictedDiagonalGenerator s t h g :=
  (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)).forget.mapIso
    (reversedDeligneGeneratorIso s t (pullbackSimple s g) (pullbackSimple t (h ▸ g)))

/-- Only the generating label can have a nonzero coordinate. -/
theorem restrictedDiagonalGenerator_support (s t : Twist) (h : s.group = t.group)
    (g k : s.group) (hk : k ≠ g) :
    reference.data.id (restrictedDiagonalGenerator s t h g k).val = reference.data.zero :=
  reversedExteriorGenerator_support s t g (h ▸ g) (k, h ▸ k)
    (fun he => hk (congrArg Prod.fst he))

/-- The surviving coordinate is the nonzero tensor of two simple representatives. -/
theorem restrictedDiagonalGenerator_coordinate_ne_zero (s t : Twist)
    (h : s.group = t.group) (g : s.group) :
    reference.data.id (restrictedDiagonalGenerator s t h g g).val ≠ reference.data.zero :=
  exteriorGenerator_coordinate_ne_zero t s (h ▸ g) g

theorem restrictedDiagonalGenerator_id_ne_zero (s t : Twist)
    (h : s.group = t.group) (g : s.group) :
    𝟙 (restrictedDiagonalGenerator s t h g) ≠ 0 := by
  intro he
  let F := RMod.Legacy.Hierarchy.evenForget
    (oldPullback (diagonalRestrictedTwist s t h).val).toWeaklyPointedSuperfusion
  have he' := congrArg (fun u => (F.map u).hom g) he
  rw [F.map_id, F.map_zero] at he'
  exact restrictedDiagonalGenerator_coordinate_ne_zero s t h g he'

attribute [local irreducible] stack stackInclusion stackRestriction

/-- The actual comparison image generates the entire restricted pullback. -/
theorem stackRestriction_generates (s t : Twist) (h : s.group = t.group)
    (W : Even (pullback (diagonalRestrictedTwist s t h).val)) :
    AddPiHull (pullback (diagonalRestrictedTwist s t h).val)
      (fun X : stack s t h => evenObj _ ((stackRestriction s t h).obj X)) W := by
  apply AddPiHull.of_simple_retracts
  intro X hX _
  obtain ⟨g, hlabel⟩ := pullbackSimple_cover (diagonalRestrictedTwist s t h).val X hX
  obtain ⟨S, hS, ⟨r⟩⟩ := exists_simple_retract
    (pullback (diagonalRestrictedTwist s t h).val) (restrictedDiagonalGenerator s t h g)
    (restrictedDiagonalGenerator_id_ne_zero s t h g)
  have hrep := simple_retract_supported (diagonalRestrictedTwist s t h).val g
    (restrictedDiagonalGenerator s t h g) S hS r (restrictedDiagonalGenerator_support s t h g)
  have hmem : AddPiHull (pullback (diagonalRestrictedTwist s t h).val)
      (fun X : stack s t h => evenObj _ ((stackRestriction s t h).obj X)) S :=
    AddPiHull.of_retract r ((AddPiHull.iso_iff (stackRestrictionGeneratorIso s t h g)).mp
      (AddPiHull.generator (stackGenerator s t h g)))
  exact AddPiHull.of_orbit (orbit_symm hlabel) (AddPiHull.of_orbit hrep hmem)

/-- The underlying even functor is an equivalence, with no finite hexagon assumptions. -/
theorem stackRestriction_isEquivalence (s t : Twist) (h : s.group = t.group) :
    (stackRestriction s t h).forget.IsEquivalence :=
  isEquivalence_of_hull_generation (stackRestriction s t h)
    (stackRestriction_bijective s t h) (stackRestriction_generates s t h)

/-- Equality transport of the target preserves the ordinary equivalence. -/
theorem transportSuperTarget_isEquivalence {C D E : WeaklyPointedFusionPiSuperCat}
    (h : D = E) (F : SuperFunctor C D) (hF : F.forget.IsEquivalence) :
    (transportSuperTarget h F).forget.IsEquivalence := by
  subst E
  exact hF

attribute [local irreducible] stackTwistMulFunctor transportSuperTarget

/-- The functor with the public twistMul target is an ordinary equivalence. -/
theorem stackTwistMulFunctor_isEquivalence {G : FiniteGrp.{0}} (s t : TwistOn G) :
    (stackTwistMulFunctor s t).forget.IsEquivalence := by
  unfold stackTwistMulFunctor
  exact transportSuperTarget_isEquivalence
    (congrArg pullback (diagonalRestrictedTwist_eq_mul s t))
    (stackRestriction s.val t.val (s.property.trans t.property.symm))
    (stackRestriction_isEquivalence s.val t.val (s.property.trans t.property.symm))

end RMod.BrundanEllis.Stacking
