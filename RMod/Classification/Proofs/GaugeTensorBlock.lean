import RMod.Classification.Instances.GaugeTensorBlock
import RMod.Classification.Proofs.GaugeLocalNaturality
import RMod.Classification.Proofs.IndexedMorphismEquality

/-!
# The gauge blocks are even isomorphisms natural on all input maps

The reindexing square follows from equality elimination on the actual
indexed objects and maps. Composing it with local gauge naturality keeps
the specified scalar and equality map in both sides of the square.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (d : GaugeData s.data t.data) (hρ : ∀ g, t.data.rho (d.phi g) = s.data.rho g)
  (hν : ∀ g h, t.data.nu (d.phi g) (d.phi h) =
    s.data.nu g h + d.lam h + d.lam (g * h) + d.lam g)

theorem gaugeTensorBlock_evenIso (X Y : PullbackObj C s.data) (k l : t.data.group) :
    EvenIsoLaws C.toWeaklyPointedSuperfusionData (gaugeTensorBlockData C hC s t d hρ hν X Y k l) :=
  (hC.pi.gaugeLocalTensorator_evenIso hC.toWeaklyPointedSuperfusionLaws _ _ _ _ _ _ _ _ _).trans
    hC.toWeaklyPointedSuperfusionLaws (EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws _)

theorem gaugeTensorBlock_naturality {X X' Y Y' : PullbackObj C s.data}
    (f : PullbackHom C s.data X X') (q : PullbackHom C s.data Y Y') (k l : t.data.group) :
    C.comp (twistSummandHom C t.data
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.map f)
      ((gaugeUnderlyingFunctor C hC s t d.phi d.lam hρ).data.map q) l (l⁻¹ * k))
      (gaugeTensorBlockData C hC s t d hρ hν X' Y' k l).hom =
    C.comp (gaugeTensorBlockData C hC s t d hρ hν X Y k l).hom
      (C.tensorHom (twistSummandHom C s.data f q (d.phi.symm l)
        ((d.phi.symm l)⁻¹ * d.phi.symm k)) (C.id (C.pi.factor (d.lam (d.phi.symm k))))) := by
  apply iso_naturality_trans hC.toWeaklyPointedSuperfusionLaws
  · exact hC.pi.gaugeLocalTensorator_naturality hC.toWeaklyPointedSuperfusionLaws
      (f (d.phi.symm l)) (q (d.phi.symm (l⁻¹ * k))) _ _ _ _ _ _ _
  · exact indexed_morphism_eq_naturality
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (fun i => C.tensorObj (twistSummand C s.data X Y (d.phi.symm l) i)
        (C.pi.factor (d.lam (d.phi.symm k))))
      (fun i => C.tensorObj (twistSummand C s.data X' Y' (d.phi.symm l) i)
        (C.pi.factor (d.lam (d.phi.symm k))))
      (fun i => C.tensorHom (twistSummandHom C s.data f q (d.phi.symm l) i)
        (C.id (C.pi.factor (d.lam (d.phi.symm k)))))
      (gaugeComplementaryIndex d k l) _ _

end RMod.Classification
