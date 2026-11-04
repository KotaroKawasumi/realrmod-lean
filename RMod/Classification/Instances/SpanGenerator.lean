import RMod.Classification.Abstract.HomogeneousSpan
import RMod.Classification.Proofs.HomogeneousSums

/-!
# The generator as an object of its own homogeneous span

The one-term identity decomposition places the generator in the full
subcategory. This object is used to evaluate natural transformations and
to determine them on all homogeneous sums.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusion.{0, 0}) (S : C.data.Obj)

theorem spanGenerator_mem : InHomogeneousSpan C S S := by
  obtain ⟨d, hd⟩ := exists_homogeneousSum C.laws
    (fun _ : Fin 1 => SameParityOrbit.refl C.laws S) (decomposition_singleton C.laws S)
  exact ⟨1, ⟨⟨d, hd⟩⟩⟩

def spanGenerator : HomogeneousSpanCategory C S := ⟨S, spanGenerator_mem C S⟩

end RMod.Classification
