import RMod.Classification.Proofs.GaugeLocalNormalizers

/-!
# Equality transport of the final gauge parity

Only the output parity proof changes. Equality elimination identifies
the actual local tensorators and reduces the retained equality map to
the identity. This is used for the two parenthesizations of a product.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}} (hC : WeaklyPointedSuperfusionLaws C) (p : PiData C)

include hC

theorem gaugeLocalTensorator_output_parity (X Y : C.Obj) (a b n' n c c' : ZMod 2)
    (e : c = c') (h : (a + b) + n' = n + c) (h' : (a + b) + n' = n + c') (beta : ℝˣ) :
    C.comp (p.gaugeLocalTensorator X Y a b n' n c h beta).hom
      (IsoData.ofEq C (congrArg (fun q =>
        C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor n)) (p.factor q)) e)).hom =
      (p.gaugeLocalTensorator X Y a b n' n c' h' beta).hom := by
  cases e
  exact hC.comp_id _

end RMod.Classification.PiLaws
