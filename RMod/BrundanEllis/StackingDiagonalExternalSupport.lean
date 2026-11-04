import RMod.BrundanEllis.StackingHullZero
import RMod.BrundanEllis.StackingStack
import RMod.BrundanEllis.StackingExternalReversedGeneration
import RMod.BrundanEllis.StackingKaroubiExtension

/-! The completed reversed exterior functor sends the prescribed diagonal
hull to families supported on the graph of the label identification. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
attribute [local irreducible] reversedExteriorPairing

/-- The concrete enriched extension, on the public Deligne carrier. -/
def reversedDeligneFunctor (s t : Twist) :
    SuperFunctor (deligne (pullback s) (pullback t)) (exteriorModel s t) :=
  KaroubiSuper.extension (reversedExteriorPairing s t)

theorem reversedDeligneFunctor_bijective (s t : Twist)
    (X Y : deligne (pullback s) (pullback t)) (a : ZMod 2) :
    Function.Bijective ((reversedDeligneFunctor s t).map X Y a) :=
  KaroubiSuper.extension_bijective (reversedExteriorPairing s t)
    (reversedExteriorPairing_bijective s t) X Y a

/-- Completion agrees with the exterior pairing on each embedded pair. -/
def reversedDeligneGeneratorIso (s t : Twist) (X : pullback s) (Y : pullback t) :
    (reversedDeligneFunctor s t).forget.obj
      (evenObj _ ((delignePairing (pullback s) (pullback t)).obj (X, Y))) ≅
      evenObj _ ((reversedExteriorPairing s t).obj (X, Y)) :=
  KaroubiSuper.extensionEmbeddingIso (reversedExteriorPairing s t) (evenObj _ (X, Y))

/-- Reversing the tensor order retains the same pair of support labels. -/
theorem reversedExteriorGenerator_support (s t : Twist) (g : s.group) (h : t.group)
    (k : s.group × t.group) (hk : k ≠ (g, h)) :
    reference.data.id (((reversedExteriorPairing s t).obj
      (pullbackSimple s g, pullbackSimple t h)) k).val = reference.data.zero := by
  rw [reversedExteriorPairing_object]
  exact exteriorGenerator_support t s h g (k.2, k.1)
    (fun he => hk (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)))

/-- Vanishing outside the graph is preserved by additive parity completion. -/
theorem reversedDeligne_hull_support (s t : Twist) (φ : s.group ≃* t.group)
    (X : Even (deligne (pullback s) (pullback t)))
    (hX : AddPiHull (deligne (pullback s) (pullback t))
      (diagonalGenerator s t φ (deligne (pullback s) (pullback t))
        (delignePairing (pullback s) (pullback t))) X)
    (k : s.group × t.group) (hk : k.2 ≠ φ k.1) :
    reference.data.id (((reversedDeligneFunctor s t).forget.obj X) k).val = reference.data.zero := by
  let D := deligne (pullback s) (pullback t)
  let Z := diagonalGenerator s t φ D (delignePairing (pullback s) (pullback t))
  let F := reversedDeligneFunctor s t
  apply pullback_hull_support (exteriorTwist s t).val (fun g => F.forget.obj (Z g)) k
  · intro g
    have hz := reversedExteriorGenerator_support s t g (φ g) k (by
      intro he
      apply hk
      rw [he])
    let e := (evaluate (exteriorTwist s t).val k).forget.mapIso
      (reversedDeligneGeneratorIso s t (pullbackSimple s g) (pullbackSimple t (φ g)))
    apply (fromOld_isZero reference _).1
    exact e.isZero_iff.mpr ((fromOld_isZero reference _).2 hz)
  · exact AddPiHull.map_super F (fun g => AddPiHull.generator g) hX

end RMod.BrundanEllis.Stacking
