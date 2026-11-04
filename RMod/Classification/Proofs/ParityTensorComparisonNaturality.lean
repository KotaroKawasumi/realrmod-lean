import RMod.Classification.Abstract.ParityTensorComparison
import RMod.Classification.Proofs.SpanMapRaw

/-!
# Even binary comparisons are natural on all morphisms

Each arbitrary map is the sum of its two homogeneous parts. Linearity
of the component functors and bilinearity of tensoring extend the
unsigned homogeneous naturality square to the full Hom spaces.
-/

set_option autoImplicit false

namespace RMod.Classification.ParityTensorComparison

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C} {p : Pi C.data} {a : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {N : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  (η : ParityTensorComparison S T U V p E H N a)

theorem naturality_all {X X' : HomogeneousSpanCategory A S.data.object}
    {Y Y' : HomogeneousSpanCategory A T.data.object} (f : X ⟶ X') (g : Y ⟶ Y') :
    C.data.comp (C.data.tensorHom (C.data.tensorHom (E.data.map f).hom (H.data.map g).hom)
      (C.data.id (p.data.factor a))) (η.data.app X' Y').hom =
    C.data.comp (η.data.app X Y).hom (N.data.map (spanTensorHom A S T f g)).hom := by
  let e : A.data.Hom X.obj X'.obj → C.data.Hom (E.data.obj X).obj (E.data.obj X').obj :=
    fun q => (E.data.map (ObjectProperty.homMk q : X ⟶ X')).hom
  let h : A.data.Hom Y.obj Y'.obj → C.data.Hom (H.data.obj Y).obj (H.data.obj Y').obj :=
    fun q => (H.data.map (ObjectProperty.homMk q : Y ⟶ Y')).hom
  let n : A.data.Hom (A.data.tensorObj X.obj Y.obj) (A.data.tensorObj X'.obj Y'.obj) →
      C.data.Hom (N.data.obj (spanTensorObj A S T X Y)).obj
        (N.data.obj (spanTensorObj A S T X' Y')).obj :=
    fun q => (N.data.map (ObjectProperty.homMk q : spanTensorObj A S T X Y ⟶ spanTensorObj A S T X' Y')).hom
  let i := C.data.id (p.data.factor a)
  let u := (η.data.app X Y).hom
  let v := (η.data.app X' Y').hom
  have he (q r : A.data.Hom X.obj X'.obj) : e (A.data.add q r) = C.data.add (e q) (e r) :=
    E.map_raw_add q r
  have hh (q r : A.data.Hom Y.obj Y'.obj) : h (A.data.add q r) = C.data.add (h q) (h r) :=
    H.map_raw_add q r
  have hn (q r : A.data.Hom (A.data.tensorObj X.obj Y.obj) (A.data.tensorObj X'.obj Y'.obj)) :
      n (A.data.add q r) = C.data.add (n q) (n r) :=
    N.map_raw_add (X := spanTensorObj A S T X Y) (Y := spanTensorObj A S T X' Y') q r
  have hs {b c : ZMod 2} (q : A.data.Hom X.obj X'.obj) (r : A.data.Hom Y.obj Y'.obj)
      (hq : A.data.IsHomogeneous b q) (hr : A.data.IsHomogeneous c r) :
      C.data.comp (C.data.tensorHom (C.data.tensorHom (e q) (h r)) i) v =
        C.data.comp u (n (A.data.tensorHom q r)) :=
    η.laws.naturality (ObjectProperty.homMk q : X ⟶ X') (ObjectProperty.homMk r : Y ⟶ Y') hq hr
  obtain ⟨f₀, f₁, hf₀, hf₁, hf⟩ := A.laws.grade_decomposition f.hom
  obtain ⟨g₀, g₁, hg₀, hg₁, hg⟩ := A.laws.grade_decomposition g.hom
  change C.data.comp (C.data.tensorHom (C.data.tensorHom (e f.hom) (h g.hom)) i) v =
    C.data.comp u (n (A.data.tensorHom f.hom g.hom))
  rw [← hf, ← hg]
  simp only [he, hh, hn, A.laws.tensor_add_left, A.laws.tensor_add_right,
    C.laws.tensor_add_left, C.laws.tensor_add_right, C.laws.add_comp, C.laws.comp_add]
  rw [hs f₀ g₀ hf₀ hg₀, hs f₀ g₁ hf₀ hg₁, hs f₁ g₀ hf₁ hg₀, hs f₁ g₁ hf₁ hg₁]

end RMod.Classification.ParityTensorComparison
