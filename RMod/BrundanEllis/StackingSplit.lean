import RMod.BrundanEllis.StackingPure
import RMod.BrundanEllis.FiniteAbelianSplitting

/-! The fixed-group stacking extension splits by choosing cyclic generators
of the finite group of degrees and lifting each by its pure twist.  The
resulting equivalence preserves the degree and the given kernel inclusion. -/
noncomputable section
set_option autoImplicit false
namespace RMod.BrundanEllis
open Stacking

private theorem degree_has_section (G : FiniteGrp.{0}) :
    ∃ s : (G →* Multiplicative (ZMod 8)) →* TwistClass G,
      Function.RightInverse s (degree G) := by
  letI : Finite (G →* Multiplicative (ZMod 8)) :=
    Finite.of_injective (fun f : G →* Multiplicative (ZMod 8) =>
      (f : G → Multiplicative (ZMod 8))) DFunLike.coe_injective
  apply exists_section_of_cyclic_lifts
  intro r n hn
  exact ⟨twistClass (pureTwist r), degree_pureTwist r, pureTwist_class_pow r n hn⟩

/-- A split extension for each finite G; no natural choice of splitting is required. -/
def stackingSplit (G : FiniteGrp.{0}) :
    TwistClass G ≃* ((G →* Multiplicative (ZMod 8)) × SHReal G) :=
  splitOfSection (degree G) (degree_has_section G).choose (degree_has_section G).choose_spec

theorem stackingSplit_data {G : FiniteGrp.{0}} (z : TwistClass G) (a : SHReal G) :
    (stackingSplit G z).1 = degree G z ∧
      stackingSplit G (a : TwistClass G) = (1, a) :=
  ⟨rfl, splitOfSection_kernel _ _ _ a⟩

end RMod.BrundanEllis
