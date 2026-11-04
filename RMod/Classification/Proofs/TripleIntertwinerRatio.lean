import RMod.Classification.Instances.TripleIntertwinerIso
import RMod.Classification.Proofs.SignedIsoNaturality
import RMod.Classification.Proofs.ParityPowers

/-!
# Triple comparison ratios supercommute with pure triple actions

Invert the first signed intertwining square and compose with the second.
Multiplication of the two signs adds the comparison degrees; their common
input degree is the sum of the three independent endomorphism degrees.
-/

set_option autoImplicit false

namespace RMod.Classification.TripleIntertwiner

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object} {a b : ZMod 2}
  (η : TripleIntertwiner S T R U V W E H K N a) (θ : TripleIntertwiner S T R U V W E H K N b)

theorem ratio_intertwines_triple {c d e : ZMod 2}
    (f : spanGenerator A S.data.object ⟶ spanGenerator A S.data.object)
    (g : spanGenerator A T.data.object ⟶ spanGenerator A T.data.object)
    (h : spanGenerator A R.data.object ⟶ spanGenerator A R.data.object)
    (hf : A.data.IsHomogeneous c f.hom) (hg : A.data.IsHomogeneous d g.hom) (hh : A.data.IsHomogeneous e h.hom) :
    C.data.comp (C.data.tensorHom (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom) (K.data.map h).hom)
      (C.data.comp η.data.inv θ.data.hom) =
    C.data.smul ((-1 : ℝ) ^ ((a + b) * ((c + d) + e)).val)
      (C.data.comp (C.data.comp η.data.inv θ.data.hom)
        (C.data.tensorHom (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom) (K.data.map h).hom)) := by
  let k := (N.data.map (tripleSpanHom A S T R f g h)).hom
  let l := C.data.tensorHom (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom) (K.data.map h).hom
  have hratio := signed_intertwining_ratio η.toIso k l θ.toIso
    (parity_power_mul_self (a * ((c + d) + e)))
    (η.laws.intertwines f g h hf hg hh) (θ.laws.intertwines f g h hf hg hh)
  rw [← parity_power_add, ← add_mul] at hratio
  exact hratio

end RMod.Classification.TripleIntertwiner
