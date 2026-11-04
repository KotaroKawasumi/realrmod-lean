import RMod.Classification.Instances.GaugeProductTriple
import RMod.Classification.Proofs.GaugeProductTensorBlock
import RMod.Classification.Proofs.ConvolutionProductPartialMaps

/-!
# The two global gauge routes on every triple insertion

The product insertion formula supplies each binary comparison. Local
gauge naturality moves the source binary inclusion through the outer
comparison. Tensor functoriality then assembles precisely the specified
source triple insertion, with all inverse-image indices retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

theorem gaugeTensorator_left_product_route (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.comp (convolutionProductLeftInsertion C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) g h k)
      (C.comp (convolutionHom C hC t.data
        (fun j => (gaugeTensoratorData C hC s t d hρ hν X Y j).hom)
        (fun j => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) j).val)
        ((g * h) * k))
        (gaugeTensoratorData C hC s t d hρ hν (convolutionObj C hC s.data X Y) Z ((g * h) * k)).hom) =
      C.comp (gaugeProductLeftLocalData C hC s t d hρ hν X Y Z g h k).hom
        (gaugeProductLeftSourceInsertion C hC s t d X Y Z g h k) := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  let i := gaugeProductBaseInclusion C hC s t d X Y g h
  let j := gaugeProductBaseInclusion C hC s t d (convolutionObj C hC s.data X Y) Z (g * h) k
  let P := C.pi.factor (d.lam (d.phi.symm (g * h)))
  let Q := C.pi.factor (t.data.nu (g * h) k)
  let R := C.pi.factor (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))
  let S := C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))
  let U := (F.data.obj Z k).val
  let V := (Z (d.phi.symm k)).val
  let u := (gaugeProductTensorBlockData C hC s t d hρ hν X Y g h).hom
  let v := (gaugeProductTensorBlockData C hC s t d hρ hν (convolutionObj C hC s.data X Y) Z (g * h) k).hom
  let v' := (C.pi.gaugeLocalTensorator (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h)) V
    (d.lam (d.phi.symm (g * h))) (d.lam (d.phi.symm k)) (t.data.nu (g * h) k)
    (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k)) (d.lam (d.phi.symm ((g * h) * k)))
    (gaugeProductParityTotal d hν (g * h) k) (d.beta (d.phi.symm (g * h)) (d.phi.symm k))).hom
  let a := C.tensorHom (C.tensorHom u (C.id U)) (C.id Q)
  let b := C.tensorHom (C.tensorHom (C.tensorHom i (C.id P)) (C.id U)) (C.id Q)
  let c := C.tensorHom (C.tensorHom (C.tensorHom i (C.id V)) (C.id R)) (C.id S)
  have hn : C.comp b v = C.comp v' c := by
    have he := hC.pi.gaugeLocalTensorator_naturality hC.toWeaklyPointedSuperfusionLaws i (C.id V)
      (d.lam (d.phi.symm (g * h))) (d.lam (d.phi.symm k)) (t.data.nu (g * h) k)
      (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k)) (d.lam (d.phi.symm ((g * h) * k)))
      (gaugeProductParityTotal d hν (g * h) k) (d.beta (d.phi.symm (g * h)) (d.phi.symm k))
    simpa only [hC.tensor_id, b, v, v', c, gaugeProductTensorBlockData, U, V, P, Q, R, S,
      F, gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData] using he
  have ht (T : C.Obj) {B D E : C.Obj} (f : C.Hom B D) (q : C.Hom D E) :
      C.tensorHom (C.comp f q) (C.id T) =
        C.comp (C.tensorHom f (C.id T)) (C.tensorHom q (C.id T)) :=
    (tensorRightLaws A T).map_comp f q
  rw [← hC.comp_assoc, convolutionProductLeftInsertion_outer_map,
    gaugeTensorator_productInclusion, hC.comp_assoc, gaugeTensorator_productInclusion]
  change C.comp (C.tensorHom (C.tensorHom (C.comp u (C.tensorHom i (C.id P))) (C.id U)) (C.id Q))
    (C.comp v (C.tensorHom j (C.id S))) = C.comp (C.comp a v') _
  rw [ht, ht]
  change C.comp (C.comp a b) (C.comp v (C.tensorHom j (C.id S))) = C.comp (C.comp a v') _
  rw [hC.comp_assoc, ← hC.comp_assoc b v, hn, hC.comp_assoc v' c, ← hC.comp_assoc a v']
  congr 1
  exact (ht S _ j).symm

theorem gaugeTensorator_right_product_route (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.comp (convolutionProductRightInsertion C hC t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) g h k)
      (C.comp (convolutionHom C hC t.data
        (fun j => C.id (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) j).val)
        (fun j => (gaugeTensoratorData C hC s t d hρ hν Y Z j).hom)
        (g * (h * k)))
        (gaugeTensoratorData C hC s t d hρ hν X (convolutionObj C hC s.data Y Z) (g * (h * k))).hom) =
      C.comp (gaugeProductRightLocalData C hC s t d hρ hν X Y Z g h k).hom
        (gaugeProductRightSourceInsertion C hC s t d X Y Z g h k) := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let F := gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ
  let i := gaugeProductBaseInclusion C hC s t d Y Z h k
  let j := gaugeProductBaseInclusion C hC s t d X (convolutionObj C hC s.data Y Z) g (h * k)
  let P := C.pi.factor (d.lam (d.phi.symm (h * k)))
  let Q := C.pi.factor (t.data.nu g (h * k))
  let R := C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))
  let S := C.pi.factor (d.lam (d.phi.symm (g * (h * k))))
  let U := (F.data.obj X g).val
  let V := (X (d.phi.symm g)).val
  let u := (gaugeProductTensorBlockData C hC s t d hρ hν Y Z h k).hom
  let v := (gaugeProductTensorBlockData C hC s t d hρ hν X (convolutionObj C hC s.data Y Z) g (h * k)).hom
  let v' := (C.pi.gaugeLocalTensorator V (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k))
    (d.lam (d.phi.symm g)) (d.lam (d.phi.symm (h * k))) (t.data.nu g (h * k))
    (s.data.nu (d.phi.symm g) (d.phi.symm (h * k))) (d.lam (d.phi.symm (g * (h * k))))
    (gaugeProductParityTotal d hν g (h * k)) (d.beta (d.phi.symm g) (d.phi.symm (h * k)))).hom
  let a := C.tensorHom (C.tensorHom (C.id U) u) (C.id Q)
  let b := C.tensorHom (C.tensorHom (C.id U) (C.tensorHom i (C.id P))) (C.id Q)
  let c := C.tensorHom (C.tensorHom (C.tensorHom (C.id V) i) (C.id R)) (C.id S)
  have hn : C.comp b v = C.comp v' c := by
    have he := hC.pi.gaugeLocalTensorator_naturality hC.toWeaklyPointedSuperfusionLaws (C.id V) i
      (d.lam (d.phi.symm g)) (d.lam (d.phi.symm (h * k))) (t.data.nu g (h * k))
      (s.data.nu (d.phi.symm g) (d.phi.symm (h * k))) (d.lam (d.phi.symm (g * (h * k))))
      (gaugeProductParityTotal d hν g (h * k)) (d.beta (d.phi.symm g) (d.phi.symm (h * k)))
    simpa only [hC.tensor_id, b, v, v', c, gaugeProductTensorBlockData, U, V, P, Q, R, S,
      F, gaugeUnderlyingFunctor, gaugeUnderlyingFunctorData] using he
  have ht (T : C.Obj) {B D E : C.Obj} (f : C.Hom B D) (q : C.Hom D E) :
      C.tensorHom (C.comp f q) (C.id T) =
        C.comp (C.tensorHom f (C.id T)) (C.tensorHom q (C.id T)) :=
    (tensorRightLaws A T).map_comp f q
  have hl (T : C.Obj) {B D E : C.Obj} (f : C.Hom B D) (q : C.Hom D E) :
      C.tensorHom (C.id T) (C.comp f q) =
        C.comp (C.tensorHom (C.id T) f) (C.tensorHom (C.id T) q) :=
    (tensorLeftLaws A T).map_comp f q
  rw [← hC.comp_assoc, convolutionProductRightInsertion_outer_map,
    gaugeTensorator_productInclusion, hC.comp_assoc, gaugeTensorator_productInclusion]
  change C.comp (C.tensorHom (C.tensorHom (C.id U) (C.comp u (C.tensorHom i (C.id P)))) (C.id Q))
    (C.comp v (C.tensorHom j (C.id S))) = C.comp (C.comp a v') _
  rw [hl, ht]
  change C.comp (C.comp a b) (C.comp v (C.tensorHom j (C.id S))) = C.comp (C.comp a v') _
  rw [hC.comp_assoc, ← hC.comp_assoc b v, hn, hC.comp_assoc v' c, ← hC.comp_assoc a v']
  congr 1
  exact (ht S _ j).symm

end RMod.Classification
