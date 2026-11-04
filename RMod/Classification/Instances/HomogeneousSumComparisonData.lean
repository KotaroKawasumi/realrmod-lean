import RMod.Classification.Abstract.HomogeneousSums
import RMod.Classification.Abstract.Normalizers

/-!
# Extending a homogeneous generator map to two sum presentations

Each summand transports the generator map across its source projection
and target inclusion. The coefficient records the sign from crossing
the generator map past that summand's parity. An inverse generator map
gives the specified reverse sum by the same formula.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomogeneousSum

variable {C : WeaklyPointedSuperfusionData.{u, v}} {S T X Y : C.Obj} {n : ℕ}

def comparisonHomData (a : ZMod 2) (d : HomogeneousSumData C S X n)
    (e : HomogeneousSumData C T Y n) (f : C.Hom S T) : C.Hom X Y :=
  C.finSum n (fun i => C.smul ((-1 : ℝ) ^ (a * d.parity i).val)
    (C.comp (d.projection i) (C.comp f (e.inclusion i))))

def comparisonIsoData (a : ZMod 2) (d : HomogeneousSumData C S X n)
    (e : HomogeneousSumData C T Y n) (t : IsoData C S T) : IsoData C X Y :=
  ⟨comparisonHomData a d e t.hom, comparisonHomData a e d t.inv⟩

end RMod.Classification.HomogeneousSum
