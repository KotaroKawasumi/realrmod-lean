import Superfusion.RMod.FromRawDCT.RealAssociatorNaturality
import Superfusion.RMod.FromRawDCT.RealAssociatorPentagon
import Superfusion.RMod.FromRawDCT.RealPairing

/-!
# Completed laws for the computable real associator

This concrete proof-only file bundles the separately proved inverse,
parity, naturality, and pentagon theorems for the exact executable
`realAssociatorData`.  It adds no coefficient table and performs no finite
calculation.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Laws for the exact endpoint-normalized data -/

/-- All associator laws for the finite coordinate category obtained from
the computably shifted real raw DCT. -/
def realAssociatorLaws : AssociatorLaws
    RealPairing.realD.data RealPairing.realD.laws
    RealPairing.realTensor.data RealPairing.realTensor.laws
    realAssociatorData where
  associator_hom_inv := RealAssociatorLaws.realAssociator_hom_inv
  associator_inv_hom := RealAssociatorLaws.realAssociator_inv_hom
  associator_hom_even := RealAssociatorLaws.realAssociatorHom_even
  associator_inv_even := RealAssociatorLaws.realAssociatorInv_even
  associator_naturality := RealAssociatorNaturality.realAssociator_naturality
  pentagon := RealAssociatorPentagon.realAssociator_pentagon

end Superfusion.RMod.FromRawDCT
