import RMod.Classification.Instances.GaugeProductTensorBlock

/-!
# Product-indexed triple gauge maps and source insertions

Both local routes use the actual target degrees. Source convolutions
keep the inverse image of each product as their output index. The
specified source inclusions carry all complementary-index transports,
and the final parity shift is tensored on the right.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

noncomputable def gaugeProductLeftLocalData (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (C.tensorObj (twistSummand C t.data
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X)
        ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y) g h)
        (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) k).val)
        (C.pi.factor (t.data.nu (g * h) k)))
      (C.tensorObj (C.tensorObj (C.tensorObj
        (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h)) (Z (d.phi.symm k)).val)
        (C.pi.factor (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))))
        (C.pi.factor (d.lam (d.phi.symm ((g * h) * k))))) :=
  (((gaugeProductTensorBlockData C hC s t d hρ hν X Y g h).tensor C.toWeaklyPointedSuperfusionData
    (IsoData.refl C.toWeaklyPointedSuperfusionData
      (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) k).val)).tensor
    C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData
      (C.pi.factor (t.data.nu (g * h) k)))).trans C.toWeaklyPointedSuperfusionData
    (C.pi.gaugeLocalTensorator (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h))
      (Z (d.phi.symm k)).val (d.lam (d.phi.symm (g * h))) (d.lam (d.phi.symm k))
      (t.data.nu (g * h) k) (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))
      (d.lam (d.phi.symm ((g * h) * k))) (gaugeProductParityTotal d hν (g * h) k)
      (d.beta (d.phi.symm (g * h)) (d.phi.symm k)))

noncomputable def gaugeProductLeftSourceInsertion (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.Hom (C.tensorObj (C.tensorObj (C.tensorObj
      (twistSummand C s.data X Y (d.phi.symm g) (d.phi.symm h)) (Z (d.phi.symm k)).val)
      (C.pi.factor (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k))))
      (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))
      (C.tensorObj (convolutionObj C hC s.data (convolutionObj C hC s.data X Y) Z
        (d.phi.symm ((g * h) * k))).val (C.pi.factor (d.lam (d.phi.symm ((g * h) * k))))) :=
  C.tensorHom (C.comp (C.tensorHom (C.tensorHom (gaugeProductBaseInclusion C hC s t d X Y g h)
    (C.id (Z (d.phi.symm k)).val)) (C.id (C.pi.factor (s.data.nu (d.phi.symm (g * h)) (d.phi.symm k)))))
    (gaugeProductBaseInclusion C hC s t d (convolutionObj C hC s.data X Y) Z (g * h) k))
    (C.id (C.pi.factor (d.lam (d.phi.symm ((g * h) * k)))))

noncomputable def gaugeProductRightLocalData (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    IsoData C.toWeaklyPointedSuperfusionData
      (C.tensorObj (C.tensorObj (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) g).val
        (twistSummand C t.data
          ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Y)
          ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj Z) h k))
        (C.pi.factor (t.data.nu g (h * k))))
      (C.tensorObj (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
        (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
        (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))))
        (C.pi.factor (d.lam (d.phi.symm (g * (h * k)))))) :=
  (((IsoData.refl C.toWeaklyPointedSuperfusionData
    (((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.obj X) g).val).tensor
    C.toWeaklyPointedSuperfusionData (gaugeProductTensorBlockData C hC s t d hρ hν Y Z h k)).tensor
    C.toWeaklyPointedSuperfusionData (IsoData.refl C.toWeaklyPointedSuperfusionData
      (C.pi.factor (t.data.nu g (h * k))))).trans C.toWeaklyPointedSuperfusionData
    (C.pi.gaugeLocalTensorator (X (d.phi.symm g)).val
      (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k))
      (d.lam (d.phi.symm g)) (d.lam (d.phi.symm (h * k)))
      (t.data.nu g (h * k)) (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))
      (d.lam (d.phi.symm (g * (h * k)))) (gaugeProductParityTotal d hν g (h * k))
      (d.beta (d.phi.symm g) (d.phi.symm (h * k))))

noncomputable def gaugeProductRightSourceInsertion (X Y Z : PullbackObj C s.data) (g h k : t.data.group) :
    C.Hom (C.tensorObj (C.tensorObj (C.tensorObj (X (d.phi.symm g)).val
      (twistSummand C s.data Y Z (d.phi.symm h) (d.phi.symm k)))
      (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k)))))
      (C.pi.factor (d.lam (d.phi.symm (g * (h * k))))))
      (C.tensorObj (convolutionObj C hC s.data X (convolutionObj C hC s.data Y Z)
        (d.phi.symm (g * (h * k)))).val (C.pi.factor (d.lam (d.phi.symm (g * (h * k)))))) :=
  C.tensorHom (C.comp (C.tensorHom (C.tensorHom (C.id (X (d.phi.symm g)).val)
    (gaugeProductBaseInclusion C hC s t d Y Z h k))
    (C.id (C.pi.factor (s.data.nu (d.phi.symm g) (d.phi.symm (h * k))))))
    (gaugeProductBaseInclusion C hC s t d X (convolutionObj C hC s.data Y Z) g (h * k)))
    (C.id (C.pi.factor (d.lam (d.phi.symm (g * (h * k))))))

end RMod.Classification
