import RMod.Classification.Instances.TwistedPullbackData
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Mathlib modules on the actual pullback Hom spaces

Composition and all real-linear operations are coordinatewise in C.
Mathlib's dependent-product module instances therefore apply to the
existing Hom carrier. Finiteness of the given group and of each Hom
space supplies finite dimensionality independently of monoidal coherence.
-/

set_option autoImplicit false

namespace RMod.Classification

@[implicit_reducible]
def PullbackCategory (C : PiSuperfusionData.{0, 0}) (_hC : ReferenceProperty C) (t : TwistData) : Type :=
  PullbackObj C t

namespace PullbackCategory

open CategoryTheory

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

instance category : Category (PullbackCategory C hC t) where
  Hom X Y := PullbackHom C t X Y
  id X g := C.id (X g).val
  comp f h g := C.comp (f g) (h g)
  id_comp f := funext fun g => hC.id_comp (f g)
  comp_id f := funext fun g => hC.comp_id (f g)
  assoc f h k := funext fun g => hC.comp_assoc (f g) (h g) (k g)

instance preadditive : Preadditive (PullbackCategory C hC t) where
  homGroup X Y := by
    letI : (g : t.group) → AddCommGroup (C.Hom (X g).val (Y g).val) := fun g =>
      (LinearCategory.preadditive
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩).homGroup _ _
    exact inferInstanceAs (AddCommGroup ((g : t.group) → C.Hom (X g).val (Y g).val))
  add_comp _ _ _ f h k := funext fun g => hC.add_comp (f g) (h g) (k g)
  comp_add _ _ _ f h k := funext fun g => hC.comp_add (f g) (h g) (k g)

instance linear : Linear ℝ (PullbackCategory C hC t) where
  homModule X Y := by
    letI : (g : t.group) → AddCommGroup (C.Hom (X g).val (Y g).val) := fun g =>
      (LinearCategory.preadditive
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩).homGroup _ _
    letI : (g : t.group) → Module ℝ (C.Hom (X g).val (Y g).val) := fun g =>
      (LinearCategory.linear
        ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩).homModule _ _
    exact inferInstanceAs (Module ℝ ((g : t.group) → C.Hom (X g).val (Y g).val))
  smul_comp _ _ _ r f h := funext fun g => hC.smul_comp r (f g) (h g)
  comp_smul _ _ _ f r h := funext fun g => hC.comp_smul r (f g) (h g)

instance finiteDimensionalHom (X Y : PullbackCategory C hC t) : FiniteDimensional ℝ (X ⟶ Y) := by
  letI : (g : t.group) → AddCommGroup (C.Hom (X g).val (Y g).val) := fun g =>
    (LinearCategory.preadditive
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩).homGroup _ _
  letI : (g : t.group) → Module ℝ (C.Hom (X g).val (Y g).val) := fun g =>
    (LinearCategory.linear
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩).homModule _ _
  letI : (g : t.group) → FiniteDimensional ℝ (C.Hom (X g).val (Y g).val) := fun g =>
    LinearCategory.finiteDimensionalHom
      ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩ (X g).val (Y g).val
  exact inferInstanceAs (FiniteDimensional ℝ ((g : t.group) → C.Hom (X g).val (Y g).val))

theorem finSum_eq_sum (ht : TwistLaws t) {X Y : PullbackCategory C hC t}
    (n : ℕ) (f : Fin n → (X ⟶ Y)) : (twistedPullbackData C hC t ht).finSum n f = ∑ i, f i := by
  induction n with
  | zero => simp [WeaklyPointedSuperfusionData.finSum]; rfl
  | succ n ih =>
    rw [WeaklyPointedSuperfusionData.finSum, Fin.sum_univ_castSucc, ih]
    rfl

theorem finSum_apply (ht : TwistLaws t) {X Y : PullbackCategory C hC t}
    (n : ℕ) (f : Fin n → (X ⟶ Y)) (g : t.group) :
    (twistedPullbackData C hC t ht).finSum n f g = C.finSum n (fun i => f i g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change C.add ((twistedPullbackData C hC t ht).finSum n (fun i => f i.castSucc) g)
        (f (Fin.last n) g) =
      C.add (C.finSum n (fun i => f i.castSucc g)) (f (Fin.last n) g)
    rw [ih]

end PullbackCategory
end RMod.Classification
