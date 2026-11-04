import RMod.BrundanEllis.StackingGroup

/-! Pulling cochains back along a group homomorphism commutes with the specified
stacking multiplication. The external product lives on the product of the two
label groups; restriction to the diagonal recovers the requested twist. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking

variable {G H K : FiniteGrp.{0}}

/-- Restriction changes only the indexing group; all cochains are precomposed. -/
def reindexData (s : TwistData) {H : FiniteGrp.{0}} (f : H →* s.group) : TwistData where
  group := H
  rho := s.rho.comp f
  nu g h := s.nu (f g) (f h)
  omega g h k := s.omega (f g) (f h) (f k)

/-- Every twist law is preserved by precomposition with a group homomorphism. -/
theorem reindexLaws (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group) :
    let d := reindexData s.toTwistData f
    RMod.Classification.TwistLaws ⟨d.group, d.rho, d.nu, d.omega⟩ := by
  refine {
    nu_one_left := ?_
    nu_one_right := ?_
    omega_one₁ := ?_
    omega_one₂ := ?_
    omega_one₃ := ?_
    cocycle := ?_
    pentagon := ?_ }
  · intro g; simpa [reindexData] using s.nu_one_left (f g)
  · intro g; simpa [reindexData] using s.nu_one_right (f g)
  · intro g h; simpa [reindexData] using s.omega_one₁ (f g) (f h)
  · intro g h; simpa [reindexData] using s.omega_one₂ (f g) (f h)
  · intro g h; simpa [reindexData] using s.omega_one₃ (f g) (f h)
  · intro g h k; simpa [reindexData] using s.cocycle (f g) (f h) (f k)
  · intro g h k l
    simpa [reindexData, realSign, RMod.Classification.realSign] using
      s.pentagon (f g) (f h) (f k) (f l)

def reindexTwist (s : Twist) {H : FiniteGrp.{0}} (f : H →* s.group) : TwistOn H :=
  let d := reindexData s.toTwistData f
  let h := reindexLaws s f
  ⟨⟨d, h.nu_one_left, h.nu_one_right, h.omega_one₁, h.omega_one₂,
    h.omega_one₃, h.cocycle, h.pentagon⟩, rfl⟩

def baseChange (f : H →* G) (s : TwistOn G) : TwistOn H :=
  reindexTwist s.val (s.property.symm ▸ f)

theorem baseChange_data (f : H →* G) (s : TwistOn G) :
    fixedRho (baseChange f s) = (fixedRho s).comp f ∧
    fixedNu (baseChange f s) = (fun g h => fixedNu s (f g) (f h)) ∧
    fixedOmega (baseChange f s) = (fun g h k => fixedOmega s (f g) (f h) (f k)) := by
  rcases s with ⟨s, hs⟩
  subst G
  exact ⟨rfl, rfl, rfl⟩

/-- Coordinate equality suffices, since the remaining fields are laws. -/
theorem fixed_ext {s t : TwistOn G} (hr : fixedRho s = fixedRho t)
    (hn : fixedNu s = fixedNu t) (hw : fixedOmega s = fixedOmega t) : s = t := by
  rcases s with ⟨⟨⟨S, r, v, a⟩, s1, s2, s3, s4, s5, s6, s7⟩, hs⟩
  rcases t with ⟨⟨⟨T, q, w, b⟩, t1, t2, t3, t4, t5, t6, t7⟩, ht⟩
  change S = G at hs
  change T = G at ht
  subst S
  subst T
  dsimp only [fixedRho, fixedNu, fixedOmega] at hr hn hw
  subst q
  subst w
  subst b
  rfl

@[simp] theorem baseChange_id (s : TwistOn G) : baseChange (MonoidHom.id G) s = s := by
  apply fixed_ext
  · exact (baseChange_data _ s).1.trans (MonoidHom.comp_id _)
  · exact (baseChange_data _ s).2.1
  · exact (baseChange_data _ s).2.2

theorem baseChange_comp (f : H →* G) (g : K →* H) (s : TwistOn G) :
    baseChange g (baseChange f s) = baseChange (f.comp g) s := by
  apply fixed_ext
  · simp only [(baseChange_data _ _).1]; rfl
  · simp only [(baseChange_data _ _).2.1]; rfl
  · simp only [(baseChange_data _ _).2.2]; rfl

/-- The closed formula is natural already on cochains, before taking gauge classes. -/
theorem baseChange_mul (f : H →* G) (s t : TwistOn G) :
    baseChange f (twistMul s t) = twistMul (baseChange f s) (baseChange f t) := by
  apply fixed_ext
  · simp only [(baseChange_data _ _).1, fixedRho_mul]
    ext g; rfl
  · simp only [(baseChange_data _ _).2.1, fixedNu_mul, (baseChange_data _ _).1]
    rfl
  · simp only [(baseChange_data _ _).2.2, fixedOmega_mul,
      (baseChange_data _ _).2.1, (baseChange_data _ _).1]
    funext g h k
    simp [stackOmega, correction, typeCorrection, cupOne, cross, map_mul]

/-- The external cochain product keeps both labels. -/
def externalTwist (s : TwistOn G) (t : TwistOn H) : TwistOn (FiniteGrp.of (G × H)) :=
  twistMul (baseChange (MonoidHom.fst G H) s) (baseChange (MonoidHom.snd G H) t)

/-- A common label restricts the external product to the closed stacking formula. -/
theorem externalTwist_diagonal (s t : TwistOn G) :
    baseChange ((MonoidHom.id G).prod (MonoidHom.id G)) (externalTwist s t) =
      twistMul s t := by
  rw [externalTwist, baseChange_mul, baseChange_comp, baseChange_comp]
  change twistMul (baseChange (MonoidHom.id G) s) (baseChange (MonoidHom.id G) t) = _
  rw [baseChange_id, baseChange_id]

end RMod.BrundanEllis.Stacking
