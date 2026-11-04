import RMod.BrundanEllis.StackingReindexTripleTransport
import RMod.Classification.Proofs.ConvolutionProductAssociatorBlock

/-! The local associator is compatible with reindexing of both cochains.
Only the given equality of nu and omega is used in this calculation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open CategoryTheory
namespace RMod.Classification
variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C)

/-- The product-indexed block formula also describes a block at arbitrary output. -/
theorem convolutionBlockIsoOfParity_general_hom (t : TwistData)
    (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
    (X Y Z : PullbackObj C t) (k g h : t.group)
    (hs : (convolutionLeftFamily C hC t X Y Z k (g * h) g).obj =
      C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z ((g * h)⁻¹ * k)).val)
        (C.pi.factor (t.nu (g * h) ((g * h)⁻¹ * k))))
    (hr : C.tensorObj
      (C.tensorObj (X g).val (twistSummand C t Y Z h ((g * h)⁻¹ * k)))
      (C.pi.factor (t.nu g (h * ((g * h)⁻¹ * k)))) =
      (convolutionRightFamily C hC t X Y Z k g h).obj) :
    (convolutionBlockIsoOfParity C hC t hν X Y Z k g h).hom.hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (C.comp (C.pi.localAssociator (X g).val (Y h).val (Z ((g * h)⁻¹ * k)).val
          (t.nu g h) (t.nu (g * h) ((g * h)⁻¹ * k)) (t.nu h ((g * h)⁻¹ * k))
          (t.nu g (h * ((g * h)⁻¹ * k))) (hν g h ((g * h)⁻¹ * k))
          (t.omega g h ((g * h)⁻¹ * k))).hom
          (IsoData.ofEq C.toWeaklyPointedSuperfusionData hr).hom) := by
  dsimp only [convolutionBlockIsoOfParity]
  generalize_proofs hC₀ hm₀ hm₁ hout hin he hlaw hlocal
  revert hm₁ hout hin he hlaw hs hr
  dsimp only [convolutionLeftFamily, convolutionRightFamily, twistSummand]
  generalize hbb : g⁻¹ * (g * h) = bb
  have hbb' : bb = h := hbb.symm.trans (inv_mul_cancel_left g h)
  clear hbb
  subst bb
  generalize hcc : (g * h)⁻¹ * k = cc
  have hcc' : cc = h⁻¹ * (g⁻¹ * k) := hcc.symm.trans (by rw [mul_inv_rev, mul_assoc])
  clear hcc
  subst cc
  generalize hdd : h * (h⁻¹ * (g⁻¹ * k)) = dd
  have hdd' : dd = g⁻¹ * k := hdd.symm.trans (mul_inv_cancel_left h _)
  clear hdd
  subst dd
  intros
  simp only [IsoData.toEvenIso, IsoData.ofEq, IsoData.refl, hC.comp_id, hC.id_comp]
  rfl

include hC in
/-- Equality of the local objects, parity bits and scalar preserves the actual local map. -/
theorem localAssociator_transport (X Y Z Z' : C.Obj) (hZ : Z = Z')
    (a b c d a' b' c' d' : ZMod 2) (ha : a = a') (hb : b = b')
    (hc : c = c') (hd : d = d') (e : a + b = c + d) (e' : a' + b' = c' + d')
    (w w' : ℝˣ) (hw : w = w')
    (hL : C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj X Y) (C.pi.factor a)) Z)
        (C.pi.factor b) =
      C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj X Y) (C.pi.factor a')) Z')
        (C.pi.factor b'))
    (hR : C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (C.pi.factor c)))
        (C.pi.factor d) =
      C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z') (C.pi.factor c')))
        (C.pi.factor d')) :
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hL).hom
      (C.pi.localAssociator X Y Z' a' b' c' d' e' w').hom =
    C.comp (C.pi.localAssociator X Y Z a b c d e w).hom
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData hR).hom := by
  subst Z'
  subst a'
  subst b'
  subst c'
  subst d'
  subst w'
  exact (hC.id_comp _).trans (hC.comp_id _).symm

include hC in
/-- A square between normalized local maps remains a square after changing endpoints. -/
theorem raw_transport_square_of_normalization
    {A A' L L' R R' B B' : C.Obj}
    (hs : A = L) (hs' : A' = L') (hr : R = B) (hr' : R' = B')
    (hA : A = A') (hB : B = B') (u : C.Hom L R) (v : C.Hom L' R')
    (hq : C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (hs.symm.trans (hA.trans hs'))).hom v =
      C.comp u (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (hr.trans (hB.trans hr'.symm))).hom) :
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hA).hom
      (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs').hom
        (C.comp v (IsoData.ofEq C.toWeaklyPointedSuperfusionData hr').hom)) =
    C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (C.comp u (IsoData.ofEq C.toWeaklyPointedSuperfusionData hr).hom))
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData hB).hom := by
  subst A
  subst A'
  subst B
  subst B'
  simpa only [IsoData.ofEq, IsoData.refl, hC.id_comp, hC.comp_id] using hq

/-- Left normalization only removes the redundant complementary group expression. -/
theorem convolutionLeftFamily_normalize (t : TwistData)
    (X Y Z : PullbackObj C t) (k g h : t.group) :
    (convolutionLeftFamily C hC t X Y Z k (g * h) g).obj =
      C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z ((g * h)⁻¹ * k)).val)
        (C.pi.factor (t.nu (g * h) ((g * h)⁻¹ * k))) := by
  simp only [convolutionLeftFamily, inv_mul_cancel_left]

/-- Right normalization identifies the two expressions for the final complementary degree. -/
theorem convolutionRightFamily_normalize (t : TwistData)
    (X Y Z : PullbackObj C t) (k g h : t.group) :
    C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h ((g * h)⁻¹ * k)))
      (C.pi.factor (t.nu g (h * ((g * h)⁻¹ * k)))) =
      (convolutionRightFamily C hC t X Y Z k g h).obj := by
  simp only [convolutionRightFamily, mul_inv_rev, mul_assoc, mul_inv_cancel_left]

variable (s t : Twist) (f : t.data.group →* s.data.group)
  (hρ : ∀ g, t.data.rho g = s.data.rho (f g))
  (hν : ∀ g h, t.data.nu g h = s.data.nu (f g) (f h))
  (hω : ∀ g h k, t.data.omega g h k = s.data.omega (f g) (f h) (f k))
  (X Y Z : PullbackObj C s.data)

include hν hω in
/-- Reindexing the cochains preserves the actual associator block. -/
theorem coordinateRestriction_associator_block (k g h : t.data.group)
    (hL : (convolutionLeftFamily C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k (g * h) g).obj =
      (convolutionLeftFamily C hC s.data X Y Z (f k) (f g * f h) (f g)).obj)
    (hR : (convolutionRightFamily C hC t.data
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k g h).obj =
      (convolutionRightFamily C hC s.data X Y Z (f k) (f g) (f h)).obj) :
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hL).hom
      (convolutionBlockIsoOfParity C hC s.data s.laws.normalizer_parity X Y Z
        (f k) (f g) (f h)).hom.hom =
    C.comp (convolutionBlockIsoOfParity C hC t.data t.laws.normalizer_parity
      ((coordinateRestrictionData C hC s t f hρ).obj X)
      ((coordinateRestrictionData C hC s t f hρ).obj Y)
      ((coordinateRestrictionData C hC s t f hρ).obj Z) k g h).hom.hom
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData hR).hom := by
  rw [convolutionBlockIsoOfParity_general_hom C hC s.data s.laws.normalizer_parity
      X Y Z (f k) (f g) (f h)
      (convolutionLeftFamily_normalize C hC s.data X Y Z (f k) (f g) (f h))
      (convolutionRightFamily_normalize C hC s.data X Y Z (f k) (f g) (f h)),
    convolutionBlockIsoOfParity_general_hom C hC t.data t.laws.normalizer_parity
      _ _ _ k g h (convolutionLeftFamily_normalize C hC t.data _ _ _ k g h)
      (convolutionRightFamily_normalize C hC t.data _ _ _ k g h)]
  apply raw_transport_square_of_normalization C hC
  have hi : f ((g * h)⁻¹ * k) = (f g * f h)⁻¹ * f k := by
    rw [map_mul, map_inv, map_mul]
  have hd : f (h * ((g * h)⁻¹ * k)) = f h * ((f g * f h)⁻¹ * f k) :=
    (map_mul f _ _).trans (congrArg (fun j => f h * j) hi)
  exact localAssociator_transport C hC (X (f g)).val (Y (f h)).val _ _
    (congrArg (fun j => (Z j).val) hi) _ _ _ _ _ _ _ _
    (hν g h)
    ((hν (g * h) ((g * h)⁻¹ * k)).trans
      (congrArg₂ s.data.nu (map_mul f g h) hi))
    ((hν h ((g * h)⁻¹ * k)).trans (congrArg (s.data.nu (f h)) hi))
    ((hν g (h * ((g * h)⁻¹ * k))).trans (congrArg (s.data.nu (f g)) hd))
    _ _ _ _ ((hω g h ((g * h)⁻¹ * k)).trans (congrArg (s.data.omega (f g) (f h)) hi)) _ _

end RMod.Classification
