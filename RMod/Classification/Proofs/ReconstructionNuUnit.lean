import RMod.Classification.Instances.ReconstructionMultiplication
import RMod.Classification.Proofs.ComponentSystemUnit

/-!
# Unit normalization of the extracted binary degree

The canonical unitor construction gives comparisons of degree zero.
Uniqueness of the comparison degree identifies these with the degrees
already chosen by reconstruction. Thus normalization is a consequence
of the actual unit maps and the comparison theorem.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

theorem reconstructionNu_one_left (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    reconstructionNu A C hC 1 g = 0 := by
  have h := (reconstructionComponentSystem A C hC).exists_leftUnitComparison g
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion 1 g) (reconstruction_target_product A C hC 1 g)
  exact ((exists_unique_reconstructionComparison_parity A C hC 1 g).choose_spec.2 0 h).symm

theorem reconstructionNu_one_right (g : SimpleOrbit A.toWeaklyPointedSuperfusion) :
    reconstructionNu A C hC g 1 = 0 := by
  have h := (reconstructionComponentSystem A C hC).exists_rightUnitComparison g
    (simpleOrbitRepresentative_mul A.toWeaklyPointedSuperfusion g 1) (reconstruction_target_product A C hC g 1)
  exact ((exists_unique_reconstructionComparison_parity A C hC g 1).choose_spec.2 0 h).symm

end RMod.Classification
