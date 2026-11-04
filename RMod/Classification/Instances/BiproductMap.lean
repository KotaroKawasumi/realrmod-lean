import RMod.Classification.Abstract.FiniteSums

/-!
# Data of maps between chosen biproducts

Extend each summand map by the source projection and target inclusion,
then sum. The formula only uses the supplied data; no inverse or proof is
chosen here. Functoriality and parity are proved in the separate laws file.
-/

set_option autoImplicit false

namespace RMod.Classification.BiproductData

variable {C : PiSuperfusionData.{0, 0}} {n : ℕ} {S T : Fin n → C.Obj}

def mapHom (b : BiproductData C S) (c : BiproductData C T)
    (f : (i : Fin n) → C.Hom (S i) (T i)) : C.Hom b.object c.object :=
  C.finSum n (fun i => C.comp (C.comp (b.projection i) (f i)) (c.inclusion i))

end RMod.Classification.BiproductData
