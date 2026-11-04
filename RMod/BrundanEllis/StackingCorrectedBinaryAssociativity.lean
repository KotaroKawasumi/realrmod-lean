import RMod.BrundanEllis.StackingReferenceWeightedTriple
import RMod.BrundanEllis.StackingCorrectedNestedBinary
import RMod.BrundanEllis.StackingTwistMulTriple

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data.toWeaklyPointedSuperfusionData
local notation "pi" => reference.data.pi
local notation "tensor" => reference.data.tensorObj

/-- Transport the local triple equation along the two additive degree
identities. Proof irrelevance retains the chosen component and parity
proofs without unfolding any reference comparison. -/
theorem referenceWeightedTriple_changeOuterDegrees
    (b c d e bL cR : ZMod 8) (eb : bL = b + d) (ec : cR = c + e)
    (A B C D E F : (R).Obj)
    (hB : InComponent R b B) (hC : InComponent R c C)
    (hD : InComponent R d D) (hE : InComponent R e E)
    (p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR : ZMod 2)
    (hp : p₁₂ + pL = p₂₃ + pR) (hq : q₁₂ + qL = q₂₃ + qR)
    (hBD : InComponent R bL (referenceParityProduct B D p₁₂))
    (hCE : InComponent R cR (referenceParityProduct C E q₂₃))
    (hu : (p₁₂ + q₁₂ + ReferenceCommutor.degree b c) +
        (pL + qL + ReferenceCommutor.degree bL e) =
      (p₂₃ + q₂₃ + ReferenceCommutor.degree d e) +
        (pR + qR + ReferenceCommutor.degree b cR))
    (ωs ωt ωu β₁₂ βL β₂₃ βR : ℝˣ)
    (hc : (referenceWeightedTripleLeftData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωs ωt β₁₂ βL).hom =
      (referenceWeightedTripleRightData b c d e A B C D E F hB hC hD hE
      p₁₂ pL p₂₃ pR q₁₂ qL q₂₃ qR hp hq ωu β₂₃ βR).hom) :
    let j₁₂ := (referenceBinaryBlockData b c A B C D hB hC p₁₂ q₁₂).scale R β₁₂
    let jL := (referenceBinaryBlockData bL e
      (referenceParityProduct A C q₁₂) (referenceParityProduct B D p₁₂) E F
      hBD hE pL qL).scale R βL
    let j₂₃ := (referenceBinaryBlockData d e C D E F hD hE p₂₃ q₂₃).scale R β₂₃
    let jR := (referenceBinaryBlockData b cR A B
      (referenceParityProduct C E q₂₃) (referenceParityProduct D F p₂₃)
      hB hCE pR qR).scale R βR
    (R).comp
      ((R).comp ((R).tensorHom ((R).tensorHom j₁₂.hom ((R).id (tensor E F)))
        ((R).id ((pi).factor (pL + qL + ReferenceCommutor.degree bL e)))) jL.hom)
      ((R).tensorHom ((pi).localAssociator A C E q₁₂ qL q₂₃ qR hq ωt).hom
        ((pi).localAssociator B D F p₁₂ pL p₂₃ pR hp ωs).hom) =
    (R).comp
      ((pi).localAssociator (tensor A B) (tensor C D) (tensor E F)
        (p₁₂ + q₁₂ + ReferenceCommutor.degree b c)
        (pL + qL + ReferenceCommutor.degree bL e)
        (p₂₃ + q₂₃ + ReferenceCommutor.degree d e)
        (pR + qR + ReferenceCommutor.degree b cR) hu ωu).hom
      ((R).comp ((R).tensorHom ((R).tensorHom ((R).id (tensor A B)) j₂₃.hom)
        ((R).id ((pi).factor (pR + qR + ReferenceCommutor.degree b cR)))) jR.hom) := by
  subst bL
  subst cR
  exact hc

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "pi" => reference.data.pi

set_option maxHeartbeats 400000 in
/-- On actual external labels, the corrected nested binary maps respect
the original twistMul associator. Only the concrete coefficient hexagons
remain as hypotheses; no braiding of either input category is assumed. -/
theorem correctedExteriorBinary_associativity (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group)
    (hl : ReferenceCommutor.LeftEquation (s.rho g).toAdd (t.rho h').toAdd (t.rho h'').toAdd)
    (hr : ReferenceCommutor.RightEquation (s.rho g).toAdd (s.rho g').toAdd (t.rho h'').toAdd) :
    let u := (exteriorTwist s t).val
    (R).comp (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
      ((R).tensorHom
        ((pi).localAssociator (Y h).val (Y' h').val (Y'' h'').val
          (t.nu h h') (t.nu (h * h') h'') (t.nu h' h'') (t.nu h (h' * h''))
          ((oldTwist t).laws.normalizer_parity h h' h'') (t.omega h h' h'')).hom
        ((pi).localAssociator (X g).val (X' g').val (X'' g'').val
          (s.nu g g') (s.nu (g * g') g'') (s.nu g' g'') (s.nu g (g' * g''))
          ((oldTwist s).laws.normalizer_parity g g' g'') (s.omega g g' g'')).hom) =
    (R).comp
      ((pi).localAssociator
        ((R).tensorObj (Y h).val (X g).val)
        ((R).tensorObj (Y' h').val (X' g').val)
        ((R).tensorObj (Y'' h'').val (X'' g'').val)
        (u.nu (g, h) (g', h')) (u.nu (g * g', h * h') (g'', h''))
        (u.nu (g', h') (g'', h'')) (u.nu (g, h) (g' * g'', h' * h''))
        ((oldTwist u).laws.normalizer_parity (g, h) (g', h') (g'', h''))
        (u.omega (g, h) (g', h') (g'', h''))).hom
      (correctedExteriorRightBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom := by
  let s' : TwistOn (FiniteGrp.of (s.group × t.group)) :=
    baseChange (MonoidHom.fst s.group t.group) ⟨s, rfl⟩
  let t' : TwistOn (FiniteGrp.of (s.group × t.group)) :=
    baseChange (MonoidHom.snd s.group t.group) ⟨t, rfl⟩
  have hc := twistMul_referenceTripleCoherence s' t' (g, h) (g', h') (g'', h'') hl hr
    (Y h).val (X g).val (Y' h').val (X' g').val (Y'' h'').val (X'' g'').val
    (X g).property (Y' h').property (X' g').property (Y'' h'').property
  have eS : (s.rho (g * g')).toAdd = (s.rho g).toAdd + (s.rho g').toAdd := by
    rw [map_mul, toAdd_mul]
  have eT : (t.rho (h' * h'')).toAdd = (t.rho h').toAdd + (t.rho h'').toAdd := by
    rw [map_mul, toAdd_mul]
  have hn := referenceWeightedTriple_changeOuterDegrees
    (s.rho g).toAdd (t.rho h').toAdd (s.rho g').toAdd (t.rho h'').toAdd
    (s.rho (g * g')).toAdd (t.rho (h' * h'')).toAdd eS eT
    (Y h).val (X g).val (Y' h').val (X' g').val (Y'' h'').val (X'' g'').val
    (X g).property (Y' h').property (X' g').property (Y'' h'').property
    (s.nu g g') (s.nu (g * g') g'') (s.nu g' g'') (s.nu g (g' * g''))
    (t.nu h h') (t.nu (h * h') h'') (t.nu h' h'') (t.nu h (h' * h''))
    ((oldTwist s).laws.normalizer_parity g g' g'')
    ((oldTwist t).laws.normalizer_parity h h' h'')
    (twistSummand_inComponent R referenceProperty (oldTwist s).data X X' g g')
    (twistSummand_inComponent R referenceProperty (oldTwist t).data Y' Y'' h' h'')
    ((oldTwist (exteriorTwist s t).val).laws.normalizer_parity (g, h) (g', h') (g'', h''))
    (s.omega g g' g'') (t.omega h h' h'') ((exteriorTwist s t).val.omega (g, h) (g', h') (g'', h''))
    (realSign (exteriorComparisonExponent s t g g' h h'))
    (realSign (exteriorComparisonExponent s t (g * g') g'' (h * h') h''))
    (realSign (exteriorComparisonExponent s t g' g'' h' h''))
    (realSign (exteriorComparisonExponent s t g (g' * g'') h (h' * h''))) hc
  dsimp only
  simp only [correctedExteriorLeftBinaryData, correctedExteriorRightBinaryData,
    IsoData.trans, IsoData.tensor, IsoData.refl, correctedExteriorBinary_hom]
  with_unfolding_all exact hn

end RMod.BrundanEllis.Stacking
