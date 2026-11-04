import Superfusion.RMod.RawDCT.ConnectorRealization
import Superfusion.RMod.RawDCT.RealConnectorFamily
import Superfusion.RMod.RawDCT.RealRawDCT

/-!
# Semantic realization of the computable raw real connector

This file exposes the two coordinate-to-semantic route maps used to compare
the computable raw connector with its semantic `ConnectorFamily`.  The maps
only reindex the stored finite coordinates and apply the canonical
coefficient realization.  They make no choice and perform no new finite
table check.

The commuting theorem identifies the stored executable forward map with the
already certified semantic connector.  Its proof is a threefold matrix-vector
calculation; no fourfold pentagon route occurs here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open GaugeChi
open RModCoordinate

/-! ## Coefficient and route realizations -/

/-- The coefficient realization, ascribed to the carrier used by the real
gauge.  This is a proof-only semantic adapter. -/
private noncomputable def semanticCoeff (a : ZMod 8) (x : Coeff a) :
    (realGauge.D a).carrier :=
  Coeff.semantic a x

private theorem semanticCoeff_sum {I : Type*} [Fintype I]
    (a : ZMod 8) (f : I → Coeff a) :
    semanticCoeff a (∑ i, f i) = ∑ i, semanticCoeff a (f i) := by
  change Coeff.semantic a (∑ i, f i) = ∑ i, Coeff.semantic a (f i)
  exact map_sum (Coeff.semantic a) f Finset.univ

private theorem semanticCoeff_mul (a : ZMod 8) (x y : Coeff a) :
    semanticCoeff a (Coeff.mul a x y) =
      semanticCoeff a x * semanticCoeff a y := by
  change Coeff.semantic a (Coeff.mul a x y) =
    Coeff.semantic a x * Coeff.semantic a y
  exact Coeff.semantic_mul a x y

/-- A raw left-route vector, read in the semantic composite left frame. -/
private noncomputable def leftSemanticColumn (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    Bimod.FusionColumn (realGauge.gaugeRouteL a b c) :=
  fun I =>
    let p := (gblIndexEquiv ℝ realGauge a b c).symm I
    semanticCoeff (a + b + c)
      (m (finSumFinEquiv p.1) (finSumFinEquiv p.2))

/-- A raw right-route vector, read in the semantic native right frame.  The
endpoint coefficient is transported along associativity. -/
private noncomputable def rightSemanticColumn (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c) :
    Bimod.FusionColumn (realGauge.gaugeRouteR a b c) :=
  fun I =>
    let p := (gbrNativeIndexEquiv ℝ realGauge a b c).symm I
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (semanticCoeff (a + b + c)
        (m (finSumFinEquiv p.1) (finSumFinEquiv p.2)))

/-- Public realization of the stored raw left-route carrier as semantic
`GBL`. -/
noncomputable def realTLeftToSemantic (a b c : ZMod 8) :
    realTData.LeftCarrier a b c → GBL realGauge a b c :=
  fun m => (gblColumnEquiv ℝ realGauge a b c).symm
    (leftSemanticColumn a b c m)

/-- Public realization of the stored raw right-route carrier as semantic
`GBR`. -/
noncomputable def realTRightToSemantic (a b c : ZMod 8) :
    realTData.RightCarrier a b c → GBR realGauge a b c :=
  fun m => (gbrNativeColumnEquiv ℝ realGauge a b c).symm
    (rightSemanticColumn a b c m)

/-! ## Frame comparison -/

/-- Reindex a raw left row pair into the semantic composite frame. -/
private noncomputable def leftPairSemanticEquiv (a b c : ZMod 8) :
    (FusionTable.Index a b × FusionTable.Index (a + b) c) ≃
      (Fin (realGauge.gaugeSizeL a b c).1 ⊕
        Fin (realGauge.gaugeSizeL a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (gblIndexEquiv ℝ realGauge a b c))

/-- Reindex a raw right row pair into the semantic native frame. -/
private noncomputable def rightPairSemanticEquiv (a b c : ZMod 8) :
    (FusionTable.Index b c × FusionTable.Index a (b + c)) ≃
      (Fin (realGauge.gaugeSizeR a b c).1 ⊕
        Fin (realGauge.gaugeSizeR a b c).2) :=
  ((finSumFinEquiv.symm.prodCongr finSumFinEquiv.symm).trans
    (gbrNativeIndexEquiv ℝ realGauge a b c))

@[simp]
private theorem leftPairSemanticEquiv_apply (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    leftPairSemanticEquiv a b c (r, s) =
      gblIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex a b r,
          FusionTable.frameIndex (a + b) c s) :=
  rfl

@[simp]
private theorem rightPairSemanticEquiv_apply (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    rightPairSemanticEquiv a b c (r, s) =
      gbrNativeIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex b c r,
          FusionTable.frameIndex a (b + c) s) :=
  rfl

@[simp]
private theorem leftPairSemanticEquiv_symm_apply (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    (gblIndexEquiv ℝ realGauge a b c).symm
        (leftPairSemanticEquiv a b c (r, s)) =
      (FusionTable.frameIndex a b r,
        FusionTable.frameIndex (a + b) c s) := by
  rw [leftPairSemanticEquiv_apply,
    (gblIndexEquiv ℝ realGauge a b c).symm_apply_apply]
  rfl

@[simp]
private theorem rightPairSemanticEquiv_symm_apply (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    (gbrNativeIndexEquiv ℝ realGauge a b c).symm
        (rightPairSemanticEquiv a b c (r, s)) =
      (FusionTable.frameIndex b c r,
        FusionTable.frameIndex a (b + c) s) := by
  rw [rightPairSemanticEquiv_apply,
    (gbrNativeIndexEquiv ℝ realGauge a b c).symm_apply_apply]
  rfl

@[simp]
private theorem leftSemanticColumn_apply_pair (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    leftSemanticColumn a b c m
        (gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b r,
            FusionTable.frameIndex (a + b) c s)) =
      semanticCoeff (a + b + c) (m r s) := by
  change semanticCoeff (a + b + c)
      (m
        (finSumFinEquiv
          ((gblIndexEquiv ℝ realGauge a b c).symm
            (leftPairSemanticEquiv a b c (r, s))).1)
        (finSumFinEquiv
          ((gblIndexEquiv ℝ realGauge a b c).symm
            (leftPairSemanticEquiv a b c (r, s))).2)) = _
  rw [leftPairSemanticEquiv_symm_apply]
  simp [FusionTable.frameIndex]

@[simp]
private theorem rightSemanticColumn_apply_pair (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    rightSemanticColumn a b c m
        (gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c r,
            FusionTable.frameIndex a (b + c) s)) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c) (m r s)) := by
  change (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
      (semanticCoeff (a + b + c)
        (m
          (finSumFinEquiv
            ((gbrNativeIndexEquiv ℝ realGauge a b c).symm
              (rightPairSemanticEquiv a b c (r, s))).1)
          (finSumFinEquiv
            ((gbrNativeIndexEquiv ℝ realGauge a b c).symm
              (rightPairSemanticEquiv a b c (r, s))).2))) = _
  rw [rightPairSemanticEquiv_symm_apply]
  simp [FusionTable.frameIndex]

@[simp]
private theorem leftSemanticColumn_apply_semanticPair (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    leftSemanticColumn a b c m (leftPairSemanticEquiv a b c (r, s)) =
      semanticCoeff (a + b + c) (m r s) := by
  rw [leftPairSemanticEquiv_apply, leftSemanticColumn_apply_pair]

@[simp]
private theorem rightSemanticColumn_apply_semanticPair (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    rightSemanticColumn a b c m (rightPairSemanticEquiv a b c (r, s)) =
      (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c) (m r s)) := by
  rw [rightPairSemanticEquiv_apply, rightSemanticColumn_apply_pair]

/-! ## Explicit inverse route realizations -/

/-- Read a semantic left-route element back in the stored raw coordinates. -/
noncomputable def realTLeftOfSemantic (a b c : ZMod 8) :
    GBL realGauge a b c → realTData.LeftCarrier a b c :=
  fun m r s =>
    (Coeff.semantic (a + b + c)).symm
      (gblColumnEquiv ℝ realGauge a b c m
        (leftPairSemanticEquiv a b c (r, s)))

/-- Read a semantic native right-route element back in the stored raw
coordinates, undoing the endpoint associativity transport. -/
noncomputable def realTRightOfSemantic (a b c : ZMod 8) :
    GBR realGauge a b c → realTData.RightCarrier a b c :=
  fun m r s =>
    (Coeff.semantic (a + b + c)).symm
      ((realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv.symm
        (gbrNativeColumnEquiv ℝ realGauge a b c m
          (rightPairSemanticEquiv a b c (r, s))))

@[simp]
private theorem realTLeftToSemantic_toColumn (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    gblColumnEquiv ℝ realGauge a b c (realTLeftToSemantic a b c m) =
      leftSemanticColumn a b c m :=
  (gblColumnEquiv ℝ realGauge a b c).apply_symm_apply _

@[simp]
private theorem realTRightToSemantic_toColumn (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c) :
    gbrNativeColumnEquiv ℝ realGauge a b c (realTRightToSemantic a b c m) =
      rightSemanticColumn a b c m :=
  (gbrNativeColumnEquiv ℝ realGauge a b c).apply_symm_apply _

/-- The explicit left inverse recovers every stored raw left-route vector. -/
theorem realTLeftOfToSemantic (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    realTLeftOfSemantic a b c (realTLeftToSemantic a b c m) = m := by
  funext r s
  change
    (Coeff.semantic (a + b + c)).symm
        (gblColumnEquiv ℝ realGauge a b c
          (realTLeftToSemantic a b c m)
          (leftPairSemanticEquiv a b c (r, s))) = m r s
  rw [realTLeftToSemantic_toColumn,
    leftSemanticColumn_apply_semanticPair]
  exact (Coeff.semantic (a + b + c)).symm_apply_apply _

/-- The raw-to-semantic left map recovers every semantic left-route
element after applying its explicit inverse. -/
theorem realTLeftToOfSemantic (a b c : ZMod 8)
    (m : GBL realGauge a b c) :
    realTLeftToSemantic a b c (realTLeftOfSemantic a b c m) = m := by
  apply (gblColumnEquiv ℝ realGauge a b c).injective
  funext I
  obtain ⟨⟨r, s⟩, rfl⟩ := (leftPairSemanticEquiv a b c).surjective I
  rw [realTLeftToSemantic_toColumn,
    leftSemanticColumn_apply_semanticPair]
  change
    Coeff.semantic (a + b + c)
        ((Coeff.semantic (a + b + c)).symm
          (gblColumnEquiv ℝ realGauge a b c m
            (leftPairSemanticEquiv a b c (r, s)))) = _
  exact (Coeff.semantic (a + b + c)).apply_symm_apply _

/-- The explicit right inverse recovers every stored raw right-route
vector. -/
theorem realTRightOfToSemantic (a b c : ZMod 8)
    (m : realTData.RightCarrier a b c) :
    realTRightOfSemantic a b c (realTRightToSemantic a b c m) = m := by
  funext r s
  change
    (Coeff.semantic (a + b + c)).symm
        ((realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv.symm
          (gbrNativeColumnEquiv ℝ realGauge a b c
            (realTRightToSemantic a b c m)
            (rightPairSemanticEquiv a b c (r, s)))) = m r s
  rw [realTRightToSemantic_toColumn,
    rightSemanticColumn_apply_semanticPair,
    (realGauge.gaugeCast
      (_root_.add_assoc a b c)).toAlgEquiv.symm_apply_apply]
  exact (Coeff.semantic (a + b + c)).symm_apply_apply _

/-- The raw-to-semantic right map recovers every semantic right-route
element after applying its explicit inverse. -/
theorem realTRightToOfSemantic (a b c : ZMod 8)
    (m : GBR realGauge a b c) :
    realTRightToSemantic a b c (realTRightOfSemantic a b c m) = m := by
  apply (gbrNativeColumnEquiv ℝ realGauge a b c).injective
  funext I
  obtain ⟨⟨r, s⟩, rfl⟩ := (rightPairSemanticEquiv a b c).surjective I
  rw [realTRightToSemantic_toColumn,
    rightSemanticColumn_apply_semanticPair]
  change
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (Coeff.semantic (a + b + c)
          ((Coeff.semantic (a + b + c)).symm
            ((realGauge.gaugeCast
              (_root_.add_assoc a b c)).toAlgEquiv.symm
              (gbrNativeColumnEquiv ℝ realGauge a b c m
                (rightPairSemanticEquiv a b c (r, s)))))) = _
  rw [(Coeff.semantic (a + b + c)).apply_symm_apply,
    (realGauge.gaugeCast
      (_root_.add_assoc a b c)).toAlgEquiv.apply_symm_apply]

/-! ## Equality with the certified semantic connector -/

private theorem sumPos_frameEquiv {p q sigma : ℕ}
    (h : p + q = sigma) (u : Fin p ⊕ Fin q) :
    sumPos u = (Superfusion.frameEquiv h u).val := by
  rcases u with u | u <;> rfl

private theorem leftSemanticFrame_val (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    (RawSemanticConnector.leftFrameEquiv a b c
      (gblIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex a b r,
          FusionTable.frameIndex (a + b) c s))).val =
      realTLeftPosition a b c r s :=
  rfl

private theorem rightSemanticFrame_val (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    (RawSemanticConnector.rightFrameEquiv a b c
      (gbrNativeIndexEquiv ℝ realGauge a b c
        (FusionTable.frameIndex b c r,
          FusionTable.frameIndex a (b + c) s))).val =
      realTRightPosition a b c r s :=
  rfl

private theorem leftSemanticFrame_sumPos (a b c : ZMod 8)
    (r : FusionTable.Index a b) (s : FusionTable.Index (a + b) c) :
    sumPos
        (gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b r,
            FusionTable.frameIndex (a + b) c s)) =
      realTLeftPosition a b c r s := by
  let I := gblIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex a b r,
      FusionTable.frameIndex (a + b) c s)
  calc
    sumPos I = (RawSemanticConnector.leftFrameEquiv a b c I).val :=
      sumPos_frameEquiv (RawSemanticConnector.leftTotal_eq_sigma a b c) I
    _ = realTLeftPosition a b c r s := leftSemanticFrame_val a b c r s

private theorem rightSemanticFrame_sumPos (a b c : ZMod 8)
    (r : FusionTable.Index b c) (s : FusionTable.Index a (b + c)) :
    sumPos
        (gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c r,
            FusionTable.frameIndex a (b + c) s)) =
      realTRightPosition a b c r s := by
  let I := gbrNativeIndexEquiv ℝ realGauge a b c
    (FusionTable.frameIndex b c r,
      FusionTable.frameIndex a (b + c) s)
  calc
    sumPos I = (RawSemanticConnector.rightFrameEquiv a b c I).val :=
      sumPos_frameEquiv (RawSemanticConnector.rightTotal_eq_sigma a b c) I
    _ = realTRightPosition a b c r s := rightSemanticFrame_val a b c r s

/-- Equality transport of coefficient vectors. -/
private def coeffCast {u v : ZMod 8} (h : u = v) : Coeff u → Coeff v :=
  cast (congrArg Coeff h)

private theorem coeffCast_apply {u v : ZMod 8} (h : u = v)
    (x : Coeff u) (g : Fin (realRepDim v.val)) :
    coeffCast h x g =
      x ((finCongr (congrArg (fun z : ZMod 8 => realRepDim z.val) h)).symm g) := by
  subst v
  rfl

private theorem semanticCoeff_cast {u v : ZMod 8} (h : u = v)
    (x : Coeff u) :
    semanticCoeff v (coeffCast h x) =
      (realGauge.gaugeCast h).toAlgEquiv (semanticCoeff u x) := by
  subst v
  rfl

private theorem semanticCoeff_gaugeCast (a b c : ZMod 8)
    (x : Coeff (a + b + c)) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c) x) =
      ∑ g : Fin (realRepDim (a + (b + c)).val),
        x ((finCongr (congrArg (fun z : ZMod 8 => realRepDim z.val)
          (_root_.add_assoc a b c))).symm g) •
          realRepBasis (a + (b + c)) g := by
  rw [← semanticCoeff_cast (_root_.add_assoc a b c) x]
  change Coeff.semantic (a + (b + c))
      (coeffCast (_root_.add_assoc a b c) x) = _
  simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply, coeffCast_apply]

/-- Each executable forward coefficient is the corresponding entry of the
already-certified native semantic matrix. -/
private theorem forwardEntry_semantic (a b c : ZMod 8)
    (targetBC : FusionTable.Index b c)
    (targetABC : FusionTable.Index a (b + c))
    (sourceAB : FusionTable.Index a b)
    (sourceABC : FusionTable.Index (a + b) c) :
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c)
          (realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)) =
      RawSemanticConnector.forwardMatrix a b c
        (gbrNativeIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex b c targetBC,
            FusionTable.frameIndex a (b + c) targetABC))
        (gblIndexEquiv ℝ realGauge a b c
          (FusionTable.frameIndex a b sourceAB,
            FusionTable.frameIndex (a + b) c sourceABC)) := by
  classical
  rw [semanticCoeff_gaugeCast,
    RawSemanticSkeletalData.forwardMatrix_eq_native_raw,
    Superfusion.matOfCoeff₂_apply]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  simp only [realTForwardEntry]
  rw [rightSemanticFrame_sumPos, leftSemanticFrame_sumPos]
  rfl

private theorem rawFinSum_eq_sum {a : ZMod 8} {n : ℕ}
    (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ r, f r := by
  change (List.ofFn f).sum = ∑ r, f r
  exact List.sum_ofFn

/-- Column form of the executable/semantic commuting square. -/
private theorem hom_semanticColumn (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    rightSemanticColumn a b c (realTData.hom a b c m) =
      gmulVecMapNative ℝ realGauge a b c
        (RawSemanticConnector.forwardMatrix a b c)
        (leftSemanticColumn a b c m) := by
  classical
  funext I
  obtain ⟨target, rfl⟩ := (rightPairSemanticEquiv a b c).surjective I
  rcases target with ⟨targetBC, targetABC⟩
  rw [rightSemanticColumn_apply_semanticPair, gmulVecMapNative_apply]
  change
    (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
        (semanticCoeff (a + b + c)
          (realTHom a b c m targetBC targetABC)) =
      ∑ J,
        RawSemanticConnector.forwardMatrix a b c
            (rightPairSemanticEquiv a b c (targetBC, targetABC)) J *
          (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
            (leftSemanticColumn a b c m J)
  unfold realTHom
  rw [rawFinSum_eq_sum]
  simp_rw [rawFinSum_eq_sum, semanticCoeff_sum,
    semanticCoeff_mul, map_sum, map_mul]
  conv_rhs =>
    rw [← Equiv.sum_comp (leftPairSemanticEquiv a b c)
      (fun J =>
        RawSemanticConnector.forwardMatrix a b c
            (rightPairSemanticEquiv a b c (targetBC, targetABC)) J *
          (realGauge.gaugeCast (_root_.add_assoc a b c)).toAlgEquiv
            (leftSemanticColumn a b c m J)),
      Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sourceAB _
  apply Finset.sum_congr rfl
  intro sourceABC _
  rw [forwardEntry_semantic, leftSemanticColumn_apply_semanticPair]
  rw [rightPairSemanticEquiv_apply, leftPairSemanticEquiv_apply]

/-- The computable raw connector commutes with its two public semantic
route realizations.  The semantic map is exactly the `T` field of
`realRawConnectorFamily`. -/
theorem realT_hom_toSemantic (a b c : ZMod 8)
    (m : realTData.LeftCarrier a b c) :
    realTRightToSemantic a b c (realTData.hom a b c m) =
      realRawConnectorFamily.T a b c (realTLeftToSemantic a b c m) := by
  change
    realTRightToSemantic a b c (realTData.hom a b c m) =
      gtOfTNative ℝ realGauge a b c
        (RawSemanticConnector.forwardMatrix a b c)
        (realTLeftToSemantic a b c m)
  apply (gbrNativeColumnEquiv ℝ realGauge a b c).injective
  rw [realTRightToSemantic_toColumn, gtOfTNative_apply,
    (gbrNativeColumnEquiv ℝ realGauge a b c).apply_symm_apply,
    realTLeftToSemantic_toColumn, hom_semanticColumn]

/-! ## Completed realization of the concrete raw real connector -/

/-- All semantic maps and their explicit coordinate inverses for the raw
real connector.  This record contains data only. -/
noncomputable def realConnectorRealizationData :
    ConnectorRealizationData realRawDCTData realGauge where
  T := realRawConnectorFamily.T
  parity := realRawConnectorFamily.parity
  leftToSemantic := realTLeftToSemantic
  leftOfSemantic := realTLeftOfSemantic
  rightToSemantic := realTRightToSemantic
  rightOfSemantic := realTRightOfSemantic

/-- The exact raw real data realize the already certified semantic
connector family. -/
theorem realConnectorRealizationLaws :
    ConnectorRealizationLaws realRawDCTData realRawDCTLaws realGauge
      realConnectorRealizationData where
  mem := realRawConnectorFamily.mem
  ne_zero := realRawConnectorFamily.ne_zero
  left_of_to := realTLeftOfToSemantic
  left_to_of := realTLeftToOfSemantic
  right_of_to := realTRightOfToSemantic
  right_to_of := realTRightToOfSemantic
  parity := by
    intro a b c
    rfl
  hom_comm := realT_hom_toSemantic

/-- Completed semantic realization of the computable raw real connector. -/
noncomputable def realConnectorRealization :
    ConnectorRealization realRawDCT realGauge where
  data := realConnectorRealizationData
  laws := realConnectorRealizationLaws

/-! The concrete realization retains a genuinely odd connector and a
nonzero semantic forward map. -/

example : realConnectorRealization.data.parity 1 1 4 = 1 := rfl

example : realConnectorRealization.data.T 0 0 0 ≠ 0 :=
  realConnectorRealization.laws.ne_zero 0 0 0

end Superfusion.RMod.RawDCT
