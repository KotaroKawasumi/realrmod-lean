import RMod.BrundanEllis.StackingExternalBinaryBlock
import RMod.BrundanEllis.StackingReferenceBinaryNaturality

/-! Naturality for the actual external convolution blocks, expressed on
homogeneous coordinate maps.  Both the original cochains and the fixed
reference tensor operations remain visible in the equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace RMod.BrundanEllis.Stacking
open RMod.Classification Superfusion.RMod.RawDCT

/-- The nu identification changes only the presentation of the source object. -/
theorem exteriorBinaryBlock_hom (s t : Twist) (X X' : pullback s) (Y Y' : pullback t)
    (g g' : s.group) (h h' : t.group) :
    (exteriorBinaryBlockData s t X X' Y Y' g g' h h').hom =
    (referenceBinaryBlockData (s.rho g).toAdd (t.rho h').toAdd
      (Y h).val (X g).val (Y' h').val (X' g').val (X g).property (Y' h').property
      (s.nu g g') (t.nu h h')).hom := by
  change reference.data.comp (reference.data.id _) _ = _
  exact referenceProperty.toWeaklyPointedSuperfusionLaws.id_comp _

/-- On homogeneous maps the only remaining sign exchanges an s-map with a t-map. -/
theorem exteriorBinaryBlock_naturality (s t : Twist)
    (X X₁ X' X₁' : pullback s) (Y Y₁ Y' Y₁' : pullback t)
    (f : PullbackHom reference.data (oldTwist s).data X X₁)
    (f' : PullbackHom reference.data (oldTwist s).data X' X₁')
    (q : PullbackHom reference.data (oldTwist t).data Y Y₁)
    (q' : PullbackHom reference.data (oldTwist t).data Y' Y₁')
    (i i' j j' : ZMod 2)
    (hf : ∀ g, reference.data.IsHomogeneous i (f g))
    (hf' : ∀ g, reference.data.IsHomogeneous i' (f' g))
    (hq : ∀ h, reference.data.IsHomogeneous j (q h))
    (hq' : ∀ h, reference.data.IsHomogeneous j' (q' h))
    (g g' : s.group) (h h' : t.group) :
    reference.data.comp
      (twistSummandHom reference.data (oldTwist (exteriorTwist s t).val).data
        (X := (reversedExteriorPairing s t).obj (X, Y))
        (X' := (reversedExteriorPairing s t).obj (X₁, Y₁))
        (Y := (reversedExteriorPairing s t).obj (X', Y'))
        (Y' := (reversedExteriorPairing s t).obj (X₁', Y₁'))
        (fun gh => reference.data.tensorHom (q gh.2) (f gh.1))
        (fun gh => reference.data.tensorHom (q' gh.2) (f' gh.1)) (g, h) (g', h'))
      (exteriorBinaryBlockData s t X₁ X₁' Y₁ Y₁' g g' h h').hom =
    reference.data.smul (paritySign (i * j'))
      (reference.data.comp (exteriorBinaryBlockData s t X X' Y Y' g g' h h').hom
        (reference.data.tensorHom
          (twistSummandHom reference.data (oldTwist t).data q q' h h')
          (twistSummandHom reference.data (oldTwist s).data f f' g g'))) := by
  rw [exteriorBinaryBlock_hom, exteriorBinaryBlock_hom]
  exact referenceBinaryBlock_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (q h) (f g) (q' h') (f' g') j i j' i' (s.nu g g') (t.nu h h')
    (hq h) (hf g) (hq' h') (hf' g')

end RMod.BrundanEllis.Stacking
