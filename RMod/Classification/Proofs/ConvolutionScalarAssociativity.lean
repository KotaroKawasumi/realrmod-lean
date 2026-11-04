import RMod.Classification.Instances.TwistOmegaReplacement
import RMod.Classification.Proofs.ConvolutionScalarProducts
import RMod.Classification.Proofs.ConvolutionProductAssociator
import RMod.Classification.Proofs.ConvolutionProductTripleExt

/-!
# The associativity equation for a scalar change of cochain

Test against each actual triple convolution insertion. The two binary
comparisons contribute their proved scalar products; the associator
contributes its specified omega. Transport the output product index
through the right route before cancelling the common equality map.
The cochain identity then identifies the full maps, not merely their
values on selected simple objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

attribute [local implicit_reducible] twistSummand

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hnu : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))
  (omega : t.group → t.group → t.group → ℝˣ) (beta : t.group → t.group → ℝˣ)

theorem convolutionScalar_associativity
    (hw : ∀ g h k, (beta g h * beta (g * h) k) * t.omega g h k =
      omega g h k * (beta h k * beta g (h * k)))
    (X Y Z : PullbackObj C t) :
    (fun q => C.comp (C.comp (convolutionHom C hC t
      (fun j => (convolutionScalarData C hC t beta X Y j).hom)
      (fun j => C.id (Z j).val) q)
      (convolutionScalarData C hC t beta (convolutionObj C hC t X Y) Z q).hom)
      (convolutionAssociatorDataOfParity C hC t hnu X Y Z q).hom) =
    (fun q => C.comp
      (convolutionAssociatorDataOfParity C hC (omegaReplacementData t omega) hnu X Y Z q).hom
      (C.comp (convolutionHom C hC t (fun j => C.id (X j).val)
        (fun j => (convolutionScalarData C hC t beta Y Z j).hom) q)
        (convolutionScalarData C hC t beta X (convolutionObj C hC t Y Z) q).hom)) := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let M : t.group → C.Obj := fun q => (convolutionObj C hC t X (convolutionObj C hC t Y Z) q).val
  let L : t.group → C.Obj := fun q => (convolutionObj C hC t (convolutionObj C hC t X Y) Z q).val
  let F : ∀ q, C.Hom (L q) (L q) := fun q => C.comp
    (convolutionHom C hC t (fun j => (convolutionScalarData C hC t beta X Y j).hom)
      (fun j => C.id (Z j).val) q)
    (convolutionScalarData C hC t beta (convolutionObj C hC t X Y) Z q).hom
  let G : ∀ q, C.Hom (M q) (M q) := fun q => C.comp
    (convolutionHom C hC t (fun j => C.id (X j).val)
      (fun j => (convolutionScalarData C hC t beta Y Z j).hom) q)
    (convolutionScalarData C hC t beta X (convolutionObj C hC t Y Z) q).hom
  let a : ∀ q, C.Hom (L q) (M q) := fun q => (convolutionAssociatorDataOfParity C hC t hnu X Y Z q).hom
  let a' : ∀ q, C.Hom (L q) (M q) := fun q =>
    (convolutionAssociatorDataOfParity C hC (omegaReplacementData t omega) hnu X Y Z q).hom
  apply hom_ext_of_convolutionProductLeftInsertions C hC t X Y Z M
  intro g h k
  let u := (g * h) * k
  let v := g * (h * k)
  let e := congrArg M (mul_assoc g h k)
  let z := (IsoData.ofEq C.toWeaklyPointedSuperfusionData e).hom
  let P := C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val)
    (C.pi.factor (t.nu (g * h) k))
  let Q := C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k))
    (C.pi.factor (t.nu g (h * k)))
  let i : C.Hom P (L u) := convolutionProductLeftInsertion C hC t X Y Z g h k
  let j : C.Hom Q (M v) := convolutionProductRightInsertion C hC t X Y Z g h k
  let b : C.Hom P Q := (C.pi.localAssociator (X g).val (Y h).val (Z k).val
    (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k)) (hnu g h k) (t.omega g h k)).hom
  let b' : C.Hom P Q := (C.pi.localAssociator (X g).val (Y h).val (Z k).val
    (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k)) (hnu g h k) (omega g h k)).hom
  let r := (beta g h * beta (g * h) k).val
  let r' := (beta h k * beta g (h * k)).val
  have hF : C.comp i (F u) = C.smul r i := convolutionScalar_left_route C hC t beta X Y Z g h k
  have hG : C.comp j (G v) = C.smul r' j := convolutionScalar_right_route C hC t beta X Y Z g h k
  have ha : C.comp (C.comp i (a u)) z = C.comp b j :=
    convolutionProductInsertion_associator C hC t hnu X Y Z g h k
  have ha' : C.comp (C.comp i (a' u)) z = C.comp b' j :=
    convolutionProductInsertion_associator C hC (omegaReplacementData t omega) hnu X Y Z g h k
  have hn : C.comp (G u) z = C.comp z (G v) :=
    indexed_morphism_eq_naturality A M M G (mul_assoc g h k) e e
  have hc : C.smul r (C.comp b j) = C.smul r' (C.comp b' j) := by
    dsimp only [b, b', PiData.localAssociator, IsoData.scale]
    simp only [hC.smul_comp, ← hC.mul_smul]
    apply congrArg (fun x : ℝ => C.smul x _)
    exact congrArg Units.val ((hw g h k).trans (mul_comm _ _))
  change C.comp i (C.comp (F u) (a u)) = C.comp i (C.comp (a' u) (G u))
  apply isoData_ofEq_cancel_right A e
  change C.comp (C.comp i (C.comp (F u) (a u))) z = C.comp (C.comp i (C.comp (a' u) (G u))) z
  calc
    _ = C.comp (C.comp (C.comp i (F u)) (a u)) z :=
      congrArg (fun m => C.comp m z) (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp (C.smul r i) (a u)) z :=
      congrArg (fun m => C.comp (C.comp m (a u)) z) hF
    _ = C.smul r (C.comp (C.comp i (a u)) z) := by rw [hC.smul_comp, hC.smul_comp]
    _ = C.smul r (C.comp b j) := congrArg (C.smul r) ha
    _ = C.smul r' (C.comp b' j) := hc
    _ = C.comp b' (C.smul r' j) := (hC.comp_smul _ _ _).symm
    _ = C.comp b' (C.comp j (G v)) := congrArg (C.comp b') hG.symm
    _ = C.comp (C.comp b' j) (G v) := (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp (C.comp i (a' u)) z) (G v) :=
      congrArg (fun m => C.comp m (G v)) ha'.symm
    _ = C.comp (C.comp i (a' u)) (C.comp z (G v)) := hC.comp_assoc _ _ _
    _ = C.comp (C.comp i (a' u)) (C.comp (G u) z) :=
      congrArg (C.comp (C.comp i (a' u))) hn.symm
    _ = _ := (hC.comp_assoc _ _ _).trans
      ((congrArg (C.comp i) (hC.comp_assoc _ _ _).symm).trans (hC.comp_assoc _ _ _).symm)

end RMod.Classification
