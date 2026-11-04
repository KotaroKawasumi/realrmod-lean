import RMod.Classification.Instances.TensorIntertwinerIso
import RMod.Classification.Proofs.SignedIsoNaturality
import RMod.Classification.Proofs.ParityPowers

/-!
# The ratio of tensor intertwiners supercommutes with pure tensor actions

The inverse of the first comparison followed by the second is an
endomorphism of the tensor of the two generator images. Its degree is
the sum of the comparison degrees, and the two naturality signs
multiply to exactly the sign of that sum.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorIntertwiner

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a b : ZMod 2}
  (η : TensorIntertwiner S T U V E H N a) (θ : TensorIntertwiner S T U V E H N b)

theorem ratio_intertwines_tensor {c d : ZMod 2}
    (f : spanGenerator C S.data.object ⟶ spanGenerator C S.data.object)
    (g : spanGenerator C T.data.object ⟶ spanGenerator C T.data.object)
    (hf : C.data.IsHomogeneous c f.hom) (hg : C.data.IsHomogeneous d g.hom) :
    D.data.comp (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)
      (D.data.comp η.data.inv θ.data.hom) =
    D.data.smul ((-1 : ℝ) ^ ((a + b) * (c + d)).val)
      (D.data.comp (D.data.comp η.data.inv θ.data.hom)
        (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)) := by
  let k := (N.data.map (ObjectProperty.homMk (C.data.tensorHom f.hom g.hom) :
    tensorSpanObject C S T ⟶ tensorSpanObject C S T)).hom
  let l := D.data.tensorHom (E.data.map f).hom (H.data.map g).hom
  have h := signed_intertwining_ratio η.toIso k l θ.toIso
    (parity_power_mul_self (a * (c + d)))
    (η.laws.intertwines f g hf hg) (θ.laws.intertwines f g hf hg)
  rw [← parity_power_add, ← add_mul] at h
  exact h

end RMod.Classification.TensorIntertwiner
