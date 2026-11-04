import RMod.BrundanEllis.StackingDiagonalExternalSupport
import RMod.BrundanEllis.StackingReindexFaithful

/-! The actual stack maps fully faithfully to the diagonal restriction of
the external cochain model. Tensor comparison and essential surjectivity
are separate obligations; neither is assumed in this construction. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking

/-- Hom bijections compose before specializing to the large pullback model. -/
theorem composite_map_bijective {C D E : Type}
    [SuperCategory C] [SuperCategory D] [SuperCategory E]
    (F : SuperFunctor C D) (J : SuperFunctor D E) (X Y : C) (a : ZMod 2)
    (hF : Function.Bijective (F.map X Y a))
    (hJ : Function.Bijective (J.map (F.obj X) (F.obj Y) a)) :
    Function.Bijective ((F.comp SuperVec J).map X Y a) := hJ.comp hF

attribute [local irreducible] stack stackInclusion reversedDeligneFunctor

/-- Retain both labels using the supplied identification of the finite groups. -/
def diagonalLabelMap (s t : Twist) (h : s.group = t.group) :
    s.group →* (exteriorTwist s t).val.group :=
  (MonoidHom.id s.group).prod (groupEqualityMulEquiv h).toMonoidHom

theorem diagonalLabelMap_injective (s t : Twist) (h : s.group = t.group) :
    Function.Injective (diagonalLabelMap s t h) := by
  intro g g' he
  exact congrArg Prod.fst he

/-- Restrict the external cochains to the same-label diagonal. -/
def diagonalRestrictedTwist (s t : Twist) (h : s.group = t.group) : TwistOn s.group :=
  reindexTwist (exteriorTwist s t).val (diagonalLabelMap s t h)

/-- Include the prescribed stack and apply the fixed completed exterior functor. -/
def stackExteriorFunctor (s t : Twist) (h : s.group = t.group) :
    SuperFunctor (stack s t h) (exteriorModel s t) :=
  (stackInclusion s t h).comp SuperVec (reversedDeligneFunctor s t)

theorem stackExteriorFunctor_bijective (s t : Twist) (h : s.group = t.group)
    (X Y : stack s t h) (a : ZMod 2) :
    Function.Bijective ((stackExteriorFunctor s t h).map X Y a) :=
  composite_map_bijective (stackInclusion s t h) (reversedDeligneFunctor s t) X Y a
    ((stack_data s t h).1 X Y a)
    (reversedDeligneFunctor_bijective s t ((stackInclusion s t h).obj X)
      ((stackInclusion s t h).obj Y) a)

/-- Every image of the actual stack is zero away from the diagonal label map. -/
theorem stackExteriorFunctor_support (s t : Twist) (h : s.group = t.group)
    (X : stack s t h) (k : (exteriorTwist s t).val.group)
    (hk : ¬ ∃ g, diagonalLabelMap s t h g = k) :
    reference.data.id ((stackExteriorFunctor s t h).obj X k).val = reference.data.zero := by
  have hX := ((stack_data s t h).2.2
    ((stackInclusion s t h).forget.obj (evenObj _ X))).mp
    ⟨evenObj _ X, ⟨Iso.refl _⟩⟩
  exact reversedDeligne_hull_support s t (groupEqualityMulEquiv h)
    ((stackInclusion s t h).forget.obj (evenObj _ X)) hX k
    (fun he => hk ⟨k.1, Prod.ext rfl he.symm⟩)

/-- This is the candidate comparison functor, before its tensorator is assembled. -/
def stackRestriction (s t : Twist) (h : s.group = t.group) :
    SuperFunctor (stack s t h) (pullback (diagonalRestrictedTwist s t h).val) :=
  (stackExteriorFunctor s t h).comp SuperVec
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h))

/-- All even and odd Hom spaces agree under the actual diagonal restriction. -/
theorem stackRestriction_bijective (s t : Twist) (h : s.group = t.group)
    (X Y : stack s t h) (a : ZMod 2) :
    Function.Bijective ((stackRestriction s t h).map X Y a) := by
  exact composite_map_bijective (stackExteriorFunctor s t h)
    (pullbackReindex (exteriorTwist s t).val (diagonalLabelMap s t h)) X Y a
    (stackExteriorFunctor_bijective s t h X Y a)
    (pullbackReindex_bijective (exteriorTwist s t).val (diagonalLabelMap s t h)
      (diagonalLabelMap_injective s t h)
      ((stackExteriorFunctor s t h).obj X) ((stackExteriorFunctor s t h).obj Y)
      (stackExteriorFunctor_support s t h X) a)

/-- The target cochains are precisely the already fixed stacking formula. -/
theorem diagonalRestrictedTwist_eq_mul {G : FiniteGrp.{0}} (s t : TwistOn G) :
    (diagonalRestrictedTwist s.val t.val (s.property.trans t.property.symm)).val =
      (twistMul s t).val := by
  rcases s with ⟨⟨⟨S, r, v, w⟩, s1, s2, s3, s4, s5, s6, s7⟩, hs⟩
  rcases t with ⟨⟨⟨T, q, z, a⟩, t1, t2, t3, t4, t5, t6, t7⟩, ht⟩
  change S = G at hs
  change T = G at ht
  subst S
  subst T
  exact congrArg Subtype.val (externalTwist_diagonal
    ⟨⟨⟨G, r, v, w⟩, s1, s2, s3, s4, s5, s6, s7⟩, rfl⟩
    ⟨⟨⟨G, q, z, a⟩, t1, t2, t3, t4, t5, t6, t7⟩, rfl⟩)

/-- Transport only the target bundle along an equality. -/
def transportSuperTarget {C D E : WeaklyPointedFusionPiSuperCat}
    (h : D = E) (F : SuperFunctor C D) : SuperFunctor C E := h ▸ F

theorem transportSuperTarget_bijective {C D E : WeaklyPointedFusionPiSuperCat}
    (h : D = E) (F : SuperFunctor C D)
    (hF : ∀ X Y a, Function.Bijective (F.map X Y a))
    (X Y : C) (a : ZMod 2) :
    Function.Bijective ((transportSuperTarget h F).map X Y a) := by
  subst E
  exact hF X Y a

/-- The concrete fully faithful comparison now has exactly the public target twist. -/
def stackTwistMulFunctor {G : FiniteGrp.{0}} (s t : TwistOn G) :
    SuperFunctor (stack s.val t.val (s.property.trans t.property.symm))
      (pullback (twistMul s t).val) :=
  transportSuperTarget (congrArg pullback (diagonalRestrictedTwist_eq_mul s t))
    (stackRestriction s.val t.val (s.property.trans t.property.symm))

attribute [local irreducible] stackTwistMulFunctor transportSuperTarget stackRestriction

theorem stackTwistMulFunctor_bijective {G : FiniteGrp.{0}} (s t : TwistOn G)
    (X Y : stack s.val t.val (s.property.trans t.property.symm)) (a : ZMod 2) :
    Function.Bijective ((stackTwistMulFunctor s t).map X Y a) := by
  unfold stackTwistMulFunctor
  exact transportSuperTarget_bijective (congrArg pullback (diagonalRestrictedTwist_eq_mul s t))
    (stackRestriction s.val t.val (s.property.trans t.property.symm))
    (stackRestriction_bijective s.val t.val (s.property.trans t.property.symm)) X Y a

end RMod.BrundanEllis.Stacking
