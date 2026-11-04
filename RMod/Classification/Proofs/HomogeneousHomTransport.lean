import RMod.Classification.Instances.HomogeneousHomTransport
import RMod.Classification.Proofs.HomogeneousHomMatrix

/-!
# Functor laws of Hom matrix transport

Entrywise algebra transport preserves identity matrices and rectangular
matrix products. Matching parity coordinates make the reconstructed maps
homogeneous of the original degree. These are the identity, composition,
and grading laws needed for the component comparison functors.
-/

set_option autoImplicit false

namespace RMod.Classification.HomogeneousSum

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S X Y Z : LinearCategory C} {T X' Y' Z' : LinearCategory D} {n m l : ℕ}
  (a : End S ≃ₐ[ℝ] End T)
  (d : HomogeneousSum C.data S X n) (e : HomogeneousSum C.data S Y m)
  (h : HomogeneousSum C.data S Z l)
  (d' : HomogeneousSum D.data T X' n) (e' : HomogeneousSum D.data T Y' m)
  (h' : HomogeneousSum D.data T Z' l)

theorem transportHom_id : transportHom a d d d' d' (𝟙 X) = 𝟙 X' := by
  apply (homMatrixLinearEquiv d' d').injective
  change toHomMatrix d' d' (transportHom a d d d' d' (𝟙 X)) = toHomMatrix d' d' (𝟙 X')
  rw [toHomMatrix_transportHom, toHomMatrix_id, toHomMatrix_id]
  exact map_one a.mapMatrix

theorem transportHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    transportHom a d h d' h' (f ≫ g) =
      transportHom a d e d' e' f ≫ transportHom a e h e' h' g := by
  apply (homMatrixLinearEquiv d' h').injective
  change toHomMatrix d' h' (transportHom a d h d' h' (f ≫ g)) =
    toHomMatrix d' h' (transportHom a d e d' e' f ≫ transportHom a e h e' h' g)
  rw [toHomMatrix_transportHom, toHomMatrix_comp d e h,
    toHomMatrix_comp d' e' h', toHomMatrix_transportHom, toHomMatrix_transportHom]
  exact Matrix.map_mul (f := a)

theorem transportHom_grade
    (ha : ∀ b (f : End S), C.data.IsHomogeneous b f → D.data.IsHomogeneous b (a f))
    (hd : d'.data.parity = d.data.parity) (he : e'.data.parity = e.data.parity)
    {b : ZMod 2} {f : X ⟶ Y} (hf : C.data.IsHomogeneous b f) :
    D.data.IsHomogeneous b (transportHom a d e d' e' f) := by
  rw [transportHom_apply]
  apply fromHomMatrix_grade d' e'
  intro i j
  rw [hd, he]
  exact ha _ _ (toHomMatrix_grade d e hf i j)

theorem transportHom_grade_iff
    (ha : ∀ b (f : End S), D.data.IsHomogeneous b (a f) ↔ C.data.IsHomogeneous b f)
    (hd : d'.data.parity = d.data.parity) (he : e'.data.parity = e.data.parity)
    {b : ZMod 2} (f : X ⟶ Y) :
    D.data.IsHomogeneous b (transportHom a d e d' e' f) ↔ C.data.IsHomogeneous b f := by
  constructor
  · intro hf
    have hm (i j) : C.data.IsHomogeneous (b + e.data.parity i + d.data.parity j)
        (toHomMatrix d e f i j) := by
      have hg := toHomMatrix_grade d' e' hf i j
      rw [toHomMatrix_transportHom, hd, he] at hg
      exact (ha _ _).mp hg
    have hg := fromHomMatrix_grade d e hm
    rwa [fromHomMatrix_toHomMatrix] at hg
  · exact transportHom_grade a d e d' e' (fun b f hf => (ha b f).mpr hf) hd he

end RMod.Classification.HomogeneousSum
