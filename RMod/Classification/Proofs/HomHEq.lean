import RMod.Classification.Proofs.Transport
import RMod.Definitions.WeaklyPointedSuperfusion

/-!
# Heterogeneous comparison of raw composites

This is equality elimination on source, intermediate and target objects.
It lets independently typed group-indexed block routes be compared while
retaining all their actual maps.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomTransport

variable (C : WeaklyPointedSuperfusionData.{u, v})

theorem comp_heq {X X' Y Y' Z Z' : C.Obj} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    {f : C.Hom X Y} {f' : C.Hom X' Y'} {g : C.Hom Y Z} {g' : C.Hom Y' Z'}
    (hf : HEq f f') (hg : HEq g g') : HEq (C.comp f g) (C.comp f' g') := by
  cases hx
  cases hy
  cases hz
  exact heq_of_eq (congrArg₂ C.comp (eq_of_heq hf) (eq_of_heq hg))

/-- A specified retraction cancels a common postcomposition even when the
source objects have different, explicitly identified group indices. -/
theorem cancel_postcomp_heq (hC : WeaklyPointedSuperfusionLaws C)
    {X X' Y Z : C.Obj} (hx : X = X') {f : C.Hom X Y} {f' : C.Hom X' Y}
    (j : C.Hom Y Z) (r : C.Hom Z Y) (hjr : C.comp j r = C.id Y)
    (he : HEq (C.comp f j) (C.comp f' j)) : HEq f f' := by
  cases hx
  apply heq_of_eq
  have h := congrArg (fun q => C.comp q r) (eq_of_heq he)
  simpa only [hC.comp_assoc, hjr, hC.comp_id] using h

end RMod.Classification.HomTransport
