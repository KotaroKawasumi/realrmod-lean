import RMod.Classification.Abstract.SpanIntertwinerIso
import RMod.Classification.Proofs.Grading
import RMod.Classification.Proofs.ParityPowers

/-!
# The inverse of a homogeneous generator comparison

The specified inverse has the same degree. Its signed intertwining
equation follows by composing the original equation with the inverse
on both sides and using that a parity sign squares to one.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanIntertwinerIso

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

def toIntertwiner (t : SpanIntertwinerIso F G a) : SpanIntertwiner F G a :=
  ⟨t.data.toSpanIntertwinerData, t.laws.toSpanIntertwinerLaws⟩

def inverseData (t : SpanIntertwinerIsoData F.data G.data) : SpanIntertwinerData G.data F.data :=
  ⟨t.inv⟩

theorem inverseLaws (t : SpanIntertwinerIso F G a) :
    SpanIntertwinerLaws a (inverseData t.data) where
  grade := homogeneous_inverse D.laws t.data.hom.hom t.data.inv.hom
    (congrArg (fun k => k.hom) t.laws.hom_inv) (congrArg (fun k => k.hom) t.laws.inv_hom)
    t.laws.grade
  intertwines {b} f hf := by
    let e : F.data.obj (spanGenerator C S) ≅ G.data.obj (spanGenerator C S) :=
      ⟨t.data.hom, t.data.inv, t.laws.hom_inv, t.laws.inv_hom⟩
    have hn : F.data.map f ≫ e.hom = ((-1 : ℝ) ^ (a * b).val) • (e.hom ≫ G.data.map f) :=
      t.laws.intertwines f hf
    have he := congrArg (fun k => e.inv ≫ k ≫ e.inv) hn
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, Iso.hom_inv_id,
      Iso.inv_hom_id_assoc, Category.comp_id] at he
    change G.data.map f ≫ e.inv = ((-1 : ℝ) ^ (a * b).val) • (e.inv ≫ F.data.map f)
    calc
      _ = ((-1 : ℝ) ^ (a * b).val) •
          (((-1 : ℝ) ^ (a * b).val) • (G.data.map f ≫ e.inv)) := by
        rw [smul_smul, parity_power_mul_self, one_smul]
      _ = _ := congrArg (fun k => ((-1 : ℝ) ^ (a * b).val) • k) he.symm

def inverse (t : SpanIntertwinerIso F G a) : SpanIntertwiner G F a :=
  ⟨inverseData t.data, inverseLaws t⟩

end RMod.Classification.SpanIntertwinerIso
