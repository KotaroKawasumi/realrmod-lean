import RMod.BrundanEllis.StackingReferenceUniformExchange

/-! A faithful linear-operator presentation of every constant-label component.
Composition is ordinary composition of right-module operators. This permits
finite coordinate identities to be reflected to the actual reference maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT

/-- Read the coefficient matrix of a morphism between row objects. -/
def rowValue {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a q)) : Matrix (Fin m) (Fin n) (Coeff a) :=
  fun j i => (f i j).coeff rfl

/-- Reading and reconstructing retains each entry of the original map. -/
theorem rowHom_rowValue {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a q)) :
    rowHom a p q (rowValue a p q f) = f := rowHom_reconstruct a p q f

/-- The actual coefficients determine the entire morphism. -/
theorem rowValue_injective {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) :
    Function.Injective (rowValue a p q) := by
  intro f g h
  have he := congrArg (rowHom a p q) h
  rw [rowHom_rowValue, rowHom_rowValue] at he
  exact he

/-- Coefficients of a composite use the stored division-algebra product. -/
theorem rowValue_comp {n m l : ℕ} (a : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (r : Fin l → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a q))
    (g : Hom realDData (rowObject a q) (rowObject a r)) :
    rowValue a p r (Hom.comp f g) = rowProduct a (rowValue a q r g) (rowValue a p q f) := by
  apply rowHom_injective a p r
  rw [← rowHom_comp]
  rw [rowHom_rowValue, rowHom_rowValue, rowHom_rowValue]

/-- Scalar multiplication is coefficientwise in this presentation. -/
theorem rowValue_smul {n m : ℕ} (a : ZMod 8) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (r : ℝ) (f : Hom realDData (rowObject a p) (rowObject a q)) :
    rowValue a p q (Hom.smul r f) = r • rowValue a p q f := by
  funext j i
  exact AtomHom.coeff_smul r (f i j) rfl

/-- Scaling all entries scales their free-module operator. -/
theorem rowOperator_smul {n m : ℕ} (a : ZMod 8) (r : ℝ)
    (M : Matrix (Fin m) (Fin n) (Coeff a)) :
    rowOperator a (r • M) = r • rowOperator a M := by
  apply LinearMap.ext
  intro v
  funext j
  simp only [rowOperator_apply, LinearMap.smul_apply, Pi.smul_apply]
  change (∑ i, Coeff.mul a (Coeff.smul a r (M j i)) (v i)) = r • ∑ i, Coeff.mul a (M j i) (v i)
  simp_rw [Coeff.smul_mul]
  change (∑ i : Fin n, r • Coeff.mul a (M j i) (v i)) = r • ∑ i, Coeff.mul a (M j i) (v i)
  exact (Finset.smul_sum (r := r) (f := fun i : Fin n => Coeff.mul a (M j i) (v i))
    (s := Finset.univ)).symm

/-- Use the original row enumeration while placing its coefficients over label `a`. -/
def uniformOperator (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData X Y) : (Fin X.size → Coeff a) →ₗ[ℝ] (Fin Y.size → Coeff a) :=
  rowOperator a (rowValue a _ _
    (homTransport (rowObject_of_labels a X hX).symm (rowObject_of_labels a Y hY).symm f))

/-- Reading a coefficient commutes with an equality transport of its two objects. -/
theorem homTransport_coeff {X Y X' Y' : Obj} (hx : X = X') (hy : Y = Y')
    (f : Hom realDData X Y) (i : Fin X.size) (j : Fin Y.size)
    (h : (X.atom i).label = (Y.atom j).label) :
    let i' := Fin.cast (congrArg Obj.size hx) i
    let j' := Fin.cast (congrArg Obj.size hy) j
    let hi : (X.atom i).label = (X'.atom i').label := by subst X'; rfl
    let hj : (Y.atom j).label = (Y'.atom j').label := by subst Y'; rfl
    (homTransport hx hy f i' j').coeff (hi.symm.trans (h.trans hj)) =
      coefficientCast hi ((f i j).coeff h) := by
  cases hx
  cases hy
  rfl

/-- The operator uses exactly the actual coefficients in the original row order. -/
theorem uniformOperator_apply (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (f : Hom realDData X Y) (v : Fin X.size → Coeff a) (j : Fin Y.size) :
    uniformOperator a X Y hX hY f v j =
      ∑ i, Coeff.mul a (coefficientCast (hX i) ((f i j).coeff ((hX i).trans (hY j).symm))) (v i) := by
  rw [uniformOperator, rowOperator_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold rowValue
  have he := homTransport_coeff (rowObject_of_labels a X hX).symm
    (rowObject_of_labels a Y hY).symm f i j ((hX i).trans (hY j).symm)
  exact congrArg (fun z => Coeff.mul a z (v i)) he

/-- This coordinate presentation is faithful, including non-simple objects. -/
theorem uniformOperator_injective (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a) :
    Function.Injective (uniformOperator a X Y hX hY) := by
  intro f g h
  have hv := rowValue_injective a _ _ (rowOperator_injective a h)
  have he := congrArg (homTransport (rowObject_of_labels a X hX) (rowObject_of_labels a Y hY)) hv
  simpa only [homTransport_roundtrip] using he

/-- Composition is preserved without any parity-dependent correction. -/
theorem uniformOperator_comp (a : ZMod 8) (X Y Z : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (hZ : ∀ k, (Z.atom k).label = a) (f : Hom realDData X Y) (g : Hom realDData Y Z) :
    uniformOperator a X Z hX hZ (Hom.comp f g) =
      (uniformOperator a Y Z hY hZ g).comp (uniformOperator a X Y hX hY f) := by
  unfold uniformOperator
  rw [homTransport_comp _ (rowObject_of_labels a Y hY).symm, rowValue_comp, rowOperator_comp]

/-- Scalar identities of operators therefore give scalar identities of actual maps. -/
theorem uniformOperator_smul (a : ZMod 8) (X Y : Obj)
    (hX : ∀ i, (X.atom i).label = a) (hY : ∀ j, (Y.atom j).label = a)
    (r : ℝ) (f : Hom realDData X Y) :
    uniformOperator a X Y hX hY (Hom.smul r f) = r • uniformOperator a X Y hX hY f := by
  unfold uniformOperator
  rw [homTransport_smul, rowValue_smul, rowOperator_smul]

end RMod.BrundanEllis.Stacking.ReferenceCommutor
