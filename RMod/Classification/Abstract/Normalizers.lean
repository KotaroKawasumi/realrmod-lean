import RMod.Classification.Abstract.ParityOperations

/-!
# Executable right-parity-factor normalizers

These are finite expressions in the abstract reference operations, with
every inverse supplied explicitly. No inverse law is used to define the
maps. The sign in the contraction is the sign fixed in the manuscript.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

variable (C : WeaklyPointedSuperfusionData.{u, v})

structure IsoData (X Y : C.Obj) where
  hom : C.Hom X Y
  inv : C.Hom Y X

structure IsoLaws {X Y : C.Obj} (d : IsoData C X Y) : Prop where
  hom_inv : C.comp d.hom d.inv = C.id X
  inv_hom : C.comp d.inv d.hom = C.id Y

structure Iso (X Y : C.Obj) where
  data : IsoData C X Y
  laws : IsoLaws C data

/-- The additional adjective required of structural comparisons in a
monoidal supercategory. Both maps remain in the underlying IsoData. -/
structure EvenIsoLaws {X Y : C.Obj} (d : IsoData C X Y) : Prop
    extends IsoLaws C d where
  hom_even : C.IsHomogeneous 0 d.hom
  inv_even : C.IsHomogeneous 0 d.inv

namespace IsoData

def refl (X : C.Obj) : IsoData C X X := ⟨C.id X, C.id X⟩

def ofEq {X Y : C.Obj} (h : X = Y) : IsoData C X Y := h ▸ refl C X

def symm {X Y : C.Obj} (d : IsoData C X Y) : IsoData C Y X := ⟨d.inv, d.hom⟩

def trans {X Y Z : C.Obj} (d : IsoData C X Y) (e : IsoData C Y Z) : IsoData C X Z :=
  ⟨C.comp d.hom e.hom, C.comp e.inv d.inv⟩

/-- Used only for even structural maps when claiming inverse laws. -/
def tensor {X X' Y Y' : C.Obj} (d : IsoData C X X') (e : IsoData C Y Y') :
    IsoData C (C.tensorObj X Y) (C.tensorObj X' Y') :=
  ⟨C.tensorHom d.hom e.hom, C.tensorHom d.inv e.inv⟩

def scale {X Y : C.Obj} (r : ℝˣ) (d : IsoData C X Y) : IsoData C X Y :=
  ⟨C.smul r.val d.hom, C.smul r⁻¹.val d.inv⟩

def assoc (X Y Z : C.Obj) :
    IsoData C (C.tensorObj (C.tensorObj X Y) Z) (C.tensorObj X (C.tensorObj Y Z)) :=
  ⟨C.associatorHom X Y Z, C.associatorInv X Y Z⟩

def leftUnit (X : C.Obj) : IsoData C (C.tensorObj C.tensorUnit X) X :=
  ⟨C.leftUnitorHom X, C.leftUnitorInv X⟩

def rightUnit (X : C.Obj) : IsoData C (C.tensorObj X C.tensorUnit) X :=
  ⟨C.rightUnitorHom X, C.rightUnitorInv X⟩

end IsoData

namespace PiData

variable {C} (p : PiData C)

/-- `P_a ⊗ P_b → P_(a+b)`, with both directions fixed. -/
def multiplyFactors (a b : ZMod 2) :
    IsoData C (C.tensorObj (p.factor a) (p.factor b)) (p.factor (a + b)) := by
  by_cases ha : a = 0
  · subst a
    simpa [factor] using IsoData.leftUnit C (p.factor b)
  · by_cases hb : b = 0
    · subst b
      simpa [factor] using IsoData.rightUnit C (p.factor a)
    · have ha1 : a = 1 := (show a = 0 ∨ a = 1 from by
        refine Fin.cases (Or.inl rfl) (fun i => ?_) a
        exact Fin.cases (Or.inr rfl) (fun j => Fin.elim0 j) i).resolve_left ha
      have hb1 : b = 1 := (show b = 0 ∨ b = 1 from by
        refine Fin.cases (Or.inl rfl) (fun i => ?_) b
        exact Fin.cases (Or.inr rfl) (fun j => Fin.elim0 j) i).resolve_left hb
      subst a; subst b
      simpa [factor, show (1 + 1 : ZMod 2) = 0 from rfl] using
        (⟨p.contractionHom, p.contractionInv⟩ :
          IsoData C (C.tensorObj p.object p.object) C.tensorUnit)

def moveFactor (a : ZMod 2) (X : C.Obj) :
    IsoData C (C.tensorObj (p.factor a) X) (C.tensorObj X (p.factor a)) := by
  by_cases ha : a = 0
  · subst a
    exact (IsoData.leftUnit C X).trans C ((IsoData.rightUnit C X).symm C)
  · exact ⟨by simpa only [factor, if_neg ha] using p.centralHom X,
      by simpa only [factor, if_neg ha] using p.centralInv X⟩

/-! The left normalizer moves the first parity factor past the third
ordinary object, then contracts the two parity factors in their order. -/

def normalLeft (X Y Z : C.Obj) (a b : ZMod 2) :
    IsoData C
      (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor a)) Z) (p.factor b))
      (C.tensorObj (C.tensorObj X (C.tensorObj Y Z)) (p.factor (a + b))) :=
  let P := p.factor a
  let Q := p.factor b
  let U := C.tensorObj X (C.tensorObj Y Z)
  let f₁ := (IsoData.assoc C (C.tensorObj X Y) P Z).tensor C (IsoData.refl C Q)
  let f₂ := ((IsoData.refl C (C.tensorObj X Y)).tensor C (p.moveFactor a Z)).tensor C
    (IsoData.refl C Q)
  let f₃ := ((IsoData.assoc C (C.tensorObj X Y) Z P).symm C).tensor C (IsoData.refl C Q)
  let f₄ := ((IsoData.assoc C X Y Z).tensor C (IsoData.refl C P)).tensor C (IsoData.refl C Q)
  let f₅ := IsoData.assoc C U P Q
  let f₆ := (IsoData.refl C U).tensor C (p.multiplyFactors a b)
  ((((f₁.trans C f₂).trans C f₃).trans C f₄).trans C f₅).trans C f₆

def normalRight (X Y Z : C.Obj) (c d : ZMod 2) :
    IsoData C
      (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor c))) (p.factor d))
      (C.tensorObj (C.tensorObj X (C.tensorObj Y Z)) (p.factor (c + d))) :=
  let U := C.tensorObj X (C.tensorObj Y Z)
  let f₁ := ((IsoData.assoc C X (C.tensorObj Y Z) (p.factor c)).symm C).tensor C
    (IsoData.refl C (p.factor d))
  let f₂ := IsoData.assoc C U (p.factor c) (p.factor d)
  let f₃ := (IsoData.refl C U).tensor C (p.multiplyFactors c d)
  (f₁.trans C f₂).trans C f₃

/-- The actual homogeneous associator `ω R⁻¹ L`, and `ω⁻¹ L⁻¹ R`.
The equality used to identify the two normal forms is only the 2-cocycle
equation; it does not assert coherence of the resulting associator. -/
def localAssociator (X Y Z : C.Obj) (a b c d : ZMod 2)
    (e : a + b = c + d) (omega : ℝˣ) :
    IsoData C
      (C.tensorObj (C.tensorObj (C.tensorObj (C.tensorObj X Y) (p.factor a)) Z) (p.factor b))
      (C.tensorObj (C.tensorObj X (C.tensorObj (C.tensorObj Y Z) (p.factor c))) (p.factor d)) :=
  ((p.normalLeft X Y Z a b).trans C
    ((IsoData.ofEq C (congrArg (fun q => C.tensorObj
      (C.tensorObj X (C.tensorObj Y Z)) (p.factor q)) e)).trans C
      ((p.normalRight X Y Z c d).symm C))).scale C omega

end PiData
end RMod.Classification
