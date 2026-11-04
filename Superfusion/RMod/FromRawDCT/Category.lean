import Superfusion.RMod.FromRawDCT.Core

/-!
# The finite coordinate category determined by `D`

This abstract file proves the category, real-linear, and grading laws of the
proof-free finite envelope from `Core.lean`.  No concrete real table or RMod
instance is constructed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace AtomHom

variable {dD : DData} (hD : DLaws dD)

private theorem algebra_mul_zero (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    d.mul x d.zero = d.zero := by
  let y := d.mul x d.zero
  have hyy : y = d.add y y := by
    calc
      y = d.mul x (d.add d.zero d.zero) := by
        exact congrArg (d.mul x) (h.zero_add d.zero).symm
      _ = d.add y y := h.mul_add x d.zero d.zero
  calc
    y = d.add d.zero y := (h.zero_add y).symm
    _ = d.add (d.add (d.neg y) y) y := by rw [h.neg_add]
    _ = d.add (d.neg y) (d.add y y) := h.add_assoc _ _ _
    _ = d.add (d.neg y) y := by rw [← hyy]
    _ = d.zero := h.neg_add y

private theorem algebra_zero_mul (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) (x : d.carrier) :
    d.mul d.zero x = d.zero := by
  let y := d.mul d.zero x
  have hyy : y = d.add y y := by
    calc
      y = d.mul (d.add d.zero d.zero) x := by
        exact congrArg (fun z => d.mul z x) (h.zero_add d.zero).symm
      _ = d.add y y := h.add_mul d.zero d.zero x
  calc
    y = d.add d.zero y := (h.zero_add y).symm
    _ = d.add (d.add (d.neg y) y) y := by rw [h.neg_add]
    _ = d.add (d.neg y) (d.add y y) := h.add_assoc _ _ _
    _ = d.add (d.neg y) y := by rw [← hyy]
    _ = d.zero := h.neg_add y

include hD

/-! ## Additive and scalar laws -/

theorem add_assoc {X Y : Atom} (f g h : AtomHom dD X Y) :
    add (add f g) h = add f (add g h) := by
  apply ext
  intro hXY
  simp only [coeff_add]
  exact (DLaws.algebra_laws hD (Atom.label X)).add_assoc _ _ _

theorem add_comm {X Y : Atom} (f g : AtomHom dD X Y) :
    add f g = add g f := by
  apply ext
  intro hXY
  simp only [coeff_add]
  exact (DLaws.algebra_laws hD (Atom.label X)).add_comm _ _

theorem zero_add {X Y : Atom} (f : AtomHom dD X Y) :
    add (zero dD X Y) f = f := by
  apply ext
  intro hXY
  simpa only [coeff_add, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).zero_add (f.coeff hXY)

theorem add_zero {X Y : Atom} (f : AtomHom dD X Y) :
    add f (zero dD X Y) = f := by
  apply ext
  intro hXY
  simpa only [coeff_add, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).add_zero (f.coeff hXY)

theorem neg_add {X Y : Atom} (f : AtomHom dD X Y) :
    add (neg f) f = zero dD X Y := by
  apply ext
  intro hXY
  simpa only [coeff_add, coeff_neg, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).neg_add (f.coeff hXY)

theorem add_neg {X Y : Atom} (f : AtomHom dD X Y) :
    add f (neg f) = zero dD X Y := by
  apply ext
  intro hXY
  simpa only [coeff_add, coeff_neg, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).add_neg (f.coeff hXY)

theorem one_smul {X Y : Atom} (f : AtomHom dD X Y) : smul 1 f = f := by
  apply ext
  intro hXY
  simpa only [coeff_smul] using
    (DLaws.algebra_laws hD (Atom.label X)).one_smul (f.coeff hXY)

theorem mul_smul {X Y : Atom} (r s : ℝ) (f : AtomHom dD X Y) :
    smul (r * s) f = smul r (smul s f) := by
  apply ext
  intro hXY
  simp only [coeff_smul]
  exact (DLaws.algebra_laws hD (Atom.label X)).smul_assoc r s (f.coeff hXY)

theorem add_smul {X Y : Atom} (r s : ℝ) (f : AtomHom dD X Y) :
    smul (r + s) f = add (smul r f) (smul s f) := by
  apply ext
  intro hXY
  simp only [coeff_smul, coeff_add]
  exact (DLaws.algebra_laws hD (Atom.label X)).add_smul r s (f.coeff hXY)

theorem smul_add {X Y : Atom} (r : ℝ) (f g : AtomHom dD X Y) :
    smul r (add f g) = add (smul r f) (smul r g) := by
  apply ext
  intro hXY
  simp only [coeff_smul, coeff_add]
  exact (DLaws.algebra_laws hD (Atom.label X)).smul_add r
    (f.coeff hXY) (g.coeff hXY)

theorem zero_smul {X Y : Atom} (f : AtomHom dD X Y) :
    smul 0 f = zero dD X Y := by
  apply ext
  intro hXY
  simpa only [coeff_smul, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).zero_smul (f.coeff hXY)

theorem smul_zero {X Y : Atom} (r : ℝ) :
    smul r (zero dD X Y) = zero dD X Y := by
  apply ext
  intro hXY
  simpa only [coeff_smul, coeff_zero] using
    (DLaws.algebra_laws hD (Atom.label X)).smul_zero r

/-! ## Category and bilinearity laws -/

theorem comp_id {X Y : Atom} (f : AtomHom dD X Y) :
    comp f (id dD Y) = f := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  by_cases hab : a = b
  · subst b
    apply ext_same_label
    simp only [coeff_comp_same_label, coeff_id]
    exact (DLaws.algebra_laws hD a).one_mul (f.coeff rfl)
  · apply eq_of_label_ne
    simpa only [Atom.label] using hab

theorem id_comp {X Y : Atom} (f : AtomHom dD X Y) :
    comp (id dD X) f = f := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  by_cases hab : a = b
  · subst b
    apply ext_same_label
    simp only [coeff_comp_same_label, coeff_id]
    exact (DLaws.algebra_laws hD a).mul_one (f.coeff rfl)
  · apply eq_of_label_ne
    simpa only [Atom.label] using hab

theorem zero_comp {X Y Z : Atom} (g : AtomHom dD Y Z) :
    comp (zero dD X Y) g = zero dD X Z := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_zero]
      exact algebra_mul_zero (dD.algebra a)
        (DLaws.algebra_laws hD a) (g.coeff rfl)
    · exact comp_eq_zero_of_right_label_ne
        (by simpa only [Atom.label] using hac) _ _
  · exact comp_eq_zero_of_left_label_ne
      (by simpa only [Atom.label] using hab) _ _

theorem comp_zero {X Y Z : Atom} (f : AtomHom dD X Y) :
    comp f (zero dD Y Z) = zero dD X Z := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_zero]
      exact algebra_zero_mul (dD.algebra a)
        (DLaws.algebra_laws hD a) (f.coeff rfl)
    · exact comp_eq_zero_of_right_label_ne
        (by simpa only [Atom.label] using hac) _ _
  · exact comp_eq_zero_of_left_label_ne
      (by simpa only [Atom.label] using hab) _ _

theorem comp_assoc {W X Y Z : Atom}
    (f : AtomHom dD W X) (g : AtomHom dD X Y)
    (h : AtomHom dD Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  rcases W with ⟨a, r⟩
  rcases X with ⟨b, s⟩
  rcases Y with ⟨c, t⟩
  rcases Z with ⟨e, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      by_cases hae : a = e
      · subst e
        apply ext_same_label
        simp only [coeff_comp_same_label]
        exact ((DLaws.algebra_laws hD a).mul_assoc
          (h.coeff rfl) (g.coeff rfl) (f.coeff rfl)).symm
      · let hAE : Atom.label (a, t) ≠ Atom.label (e, u) := by
          simpa only [Atom.label] using hae
        rw [comp_eq_zero_of_right_label_ne hAE (comp f g) h,
          comp_eq_zero_of_right_label_ne hAE g h,
          comp_zero hD f]
    · let hAC : Atom.label (a, s) ≠ Atom.label (c, t) := by
        simpa only [Atom.label] using hac
      rw [comp_eq_zero_of_right_label_ne hAC f g, zero_comp hD h,
        comp_eq_zero_of_left_label_ne hAC g h, comp_zero hD f]
  · let hAB : Atom.label (a, r) ≠ Atom.label (b, s) := by
      simpa only [Atom.label] using hab
    rw [comp_eq_zero_of_left_label_ne hAB f g, zero_comp hD h,
      comp_eq_zero_of_left_label_ne hAB f (comp g h)]

theorem add_comp {X Y Z : Atom} (f g : AtomHom dD X Y)
    (h : AtomHom dD Y Z) :
    comp (add f g) h = add (comp f h) (comp g h) := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_add]
      exact (DLaws.algebra_laws hD a).mul_add
        (h.coeff rfl) (f.coeff rfl) (g.coeff rfl)
    · let hAC : Atom.label (a, t) ≠ Atom.label (c, u) := by
        simpa only [Atom.label] using hac
      rw [comp_eq_zero_of_right_label_ne hAC (add f g) h,
        comp_eq_zero_of_right_label_ne hAC f h,
        comp_eq_zero_of_right_label_ne hAC g h,
        add_zero hD]
  · let hAB : Atom.label (a, s) ≠ Atom.label (b, t) := by
      simpa only [Atom.label] using hab
    rw [comp_eq_zero_of_left_label_ne hAB (add f g) h,
      comp_eq_zero_of_left_label_ne hAB f h,
      comp_eq_zero_of_left_label_ne hAB g h,
      add_zero hD]

theorem comp_add {X Y Z : Atom} (f : AtomHom dD X Y)
    (g h : AtomHom dD Y Z) :
    comp f (add g h) = add (comp f g) (comp f h) := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_add]
      exact (DLaws.algebra_laws hD a).add_mul
        (g.coeff rfl) (h.coeff rfl) (f.coeff rfl)
    · let hAC : Atom.label (a, t) ≠ Atom.label (c, u) := by
        simpa only [Atom.label] using hac
      rw [comp_eq_zero_of_right_label_ne hAC f (add g h),
        comp_eq_zero_of_right_label_ne hAC f g,
        comp_eq_zero_of_right_label_ne hAC f h,
        add_zero hD]
  · let hAB : Atom.label (a, s) ≠ Atom.label (b, t) := by
      simpa only [Atom.label] using hab
    rw [comp_eq_zero_of_left_label_ne hAB f (add g h),
      comp_eq_zero_of_left_label_ne hAB f g,
      comp_eq_zero_of_left_label_ne hAB f h,
      add_zero hD]

theorem smul_comp {X Y Z : Atom} (r : ℝ) (f : AtomHom dD X Y)
    (g : AtomHom dD Y Z) :
    comp (smul r f) g = smul r (comp f g) := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_smul]
      exact (DLaws.algebra_laws hD a).mul_smul r
        (g.coeff rfl) (f.coeff rfl)
    · let hAC : Atom.label (a, t) ≠ Atom.label (c, u) := by
        simpa only [Atom.label] using hac
      rw [comp_eq_zero_of_right_label_ne hAC (smul r f) g,
        comp_eq_zero_of_right_label_ne hAC f g,
        smul_zero hD]
  · let hAB : Atom.label (a, s) ≠ Atom.label (b, t) := by
      simpa only [Atom.label] using hab
    rw [comp_eq_zero_of_left_label_ne hAB (smul r f) g,
      comp_eq_zero_of_left_label_ne hAB f g,
      smul_zero hD]

theorem comp_smul {X Y Z : Atom} (r : ℝ) (f : AtomHom dD X Y)
    (g : AtomHom dD Y Z) :
    comp f (smul r g) = smul r (comp f g) := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  rcases Z with ⟨c, u⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      apply ext_same_label
      simp only [coeff_comp_same_label, coeff_smul]
      exact (DLaws.algebra_laws hD a).smul_mul r
        (g.coeff rfl) (f.coeff rfl)
    · let hAC : Atom.label (a, t) ≠ Atom.label (c, u) := by
        simpa only [Atom.label] using hac
      rw [comp_eq_zero_of_right_label_ne hAC f (smul r g),
        comp_eq_zero_of_right_label_ne hAC f g,
        smul_zero hD]
  · let hAB : Atom.label (a, s) ≠ Atom.label (b, t) := by
      simpa only [Atom.label] using hab
    rw [comp_eq_zero_of_left_label_ne hAB f (smul r g),
      comp_eq_zero_of_left_label_ne hAB f g,
      smul_zero hD]

/-! ## Atomic grading and decomposition laws -/

/- Every parity in `ZMod 2` is self-inverse. -/
omit hD in
private theorem zmod2_add_self (i : ZMod 2) : i + i = 0 := by
  revert i
  decide

/- The middle endpoint shift occurs twice in the degree of a composite and
therefore cancels. -/
omit hD in
private theorem comp_grade_index (i j r s t : ZMod 2) :
    (j + s + t) + (i + r + s) = (i + j) + r + t := by
  calc
    (j + s + t) + (i + r + s) = ((i + j) + r + t) + (s + s) := by
      ac_rfl
    _ = (i + j) + r + t := by rw [zmod2_add_self, _root_.add_zero]

theorem zero_memGrade {X Y : Atom} (i : ZMod 2) :
    MemGrade i (zero dD X Y) := by
  intro hXY
  simp only [coeff_zero, SuperAlgebraData.MemGrade]
  exact (DLaws.algebra_laws hD (Atom.label X)).component_zero _

theorem add_memGrade {X Y : Atom} {i : ZMod 2}
    (f g : AtomHom dD X Y) (hf : MemGrade i f) (hg : MemGrade i g) :
    MemGrade i (add f g) := by
  intro hXY
  simp only [coeff_add, SuperAlgebraData.MemGrade]
  rw [(DLaws.algebra_laws hD (Atom.label X)).component_add,
    hf hXY, hg hXY]

theorem neg_memGrade {X Y : Atom} {i : ZMod 2}
    (f : AtomHom dD X Y) (hf : MemGrade i f) : MemGrade i (neg f) := by
  intro hXY
  simp only [coeff_neg, SuperAlgebraData.MemGrade]
  rw [(DLaws.algebra_laws hD (Atom.label X)).component_neg, hf hXY]

theorem smul_memGrade {X Y : Atom} {i : ZMod 2} (r : ℝ)
    (f : AtomHom dD X Y) (hf : MemGrade i f) : MemGrade i (smul r f) := by
  intro hXY
  simp only [coeff_smul, SuperAlgebraData.MemGrade]
  rw [(DLaws.algebra_laws hD (Atom.label X)).component_smul, hf hXY]

/-- Projecting to parity `i` produces an `i`-homogeneous atomic morphism. -/
theorem component_memGrade {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) : MemGrade i (component i f) := by
  intro hXY
  simp only [coeff_component, SuperAlgebraData.MemGrade]
  exact (DLaws.algebra_laws hD (Atom.label X)).component_idem _ _

/-- The two stored parity projections reconstruct an atomic morphism. -/
theorem component_complement {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) :
    add (component i f) (component (i + 1) f) = f := by
  apply ext
  intro hXY
  simp only [coeff_add, coeff_component]
  have hindex :
      (i + 1) + Atom.shift X + Atom.shift Y =
        (i + Atom.shift X + Atom.shift Y) + 1 := by
    ac_rfl
  rw [hindex]
  exact (DLaws.algebra_laws hD (Atom.label X)).component_complement _ _

/-- An atomic morphism homogeneous in complementary parities is zero. -/
theorem grade_disjoint {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) (hf : MemGrade i f)
    (hf' : MemGrade (i + 1) f) : f = zero dD X Y := by
  apply ext
  intro hXY
  rw [coeff_zero]
  apply (DLaws.algebra_laws hD (Atom.label X)).grade_disjoint
    (i + Atom.shift X + Atom.shift Y) (f.coeff hXY) (hf hXY)
  have hindex :
      (i + 1) + Atom.shift X + Atom.shift Y =
        (i + Atom.shift X + Atom.shift Y) + 1 := by
    ac_rfl
  simpa only [hindex] using hf' hXY

/-- The identity on a shifted atom is even: its two endpoint shifts cancel. -/
theorem id_even (X : Atom) : MemGrade 0 (id dD X) := by
  rcases X with ⟨a, s⟩
  intro h
  change (dD.algebra a).MemGrade (0 + s + s) ((id dD (a, s)).coeff rfl)
  rw [coeff_id]
  simpa only [Atom.label, _root_.zero_add, zmod2_add_self] using
    (DLaws.algebra_laws hD a).one_mem

/-- Atomic composition adds categorical degrees. -/
theorem comp_memGrade {X Y Z : Atom} {i j : ZMod 2}
    (f : AtomHom dD X Y) (g : AtomHom dD Y Z)
    (hf : MemGrade i f) (hg : MemGrade j g) :
    MemGrade (i + j) (comp f g) := by
  rcases X with ⟨a, r⟩
  rcases Y with ⟨b, s⟩
  rcases Z with ⟨c, t⟩
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      intro h
      change (dD.algebra a).MemGrade ((i + j) + r + t)
        ((comp f g).coeff rfl)
      rw [coeff_comp_same_label]
      have hmul := (DLaws.algebra_laws hD a).mul_mem
        (j + s + t) (i + r + s) (g.coeff rfl) (f.coeff rfl)
        (hg rfl) (hf rfl)
      simpa only [comp_grade_index] using hmul
    · rw [comp_eq_zero_of_right_label_ne
        (by simpa only [Atom.label] using hac) f g]
      exact zero_memGrade hD (i + j)
  · rw [comp_eq_zero_of_left_label_ne
      (by simpa only [Atom.label] using hab) f g]
    exact zero_memGrade hD (i + j)

/-! ## Fixed-order finite-sum laws -/

/-- The interchange identity needed to separate two pointwise finite sums. -/
private theorem add_interchange {X Y : Atom}
    (w x y z : AtomHom dD X Y) :
    add (add w x) (add y z) = add (add w y) (add x z) := by
  rw [add_assoc hD w x, ← add_assoc hD x y z, add_comm hD x y,
    add_assoc hD y x z, ← add_assoc hD w y]

theorem finSum_zero {X Y : Atom} (n : ℕ) :
    finSum n (fun _ => zero dD X Y) = zero dD X Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [finSum]
      rw [ih, add_zero hD]

theorem finSum_add {X Y : Atom} {n : ℕ}
    (f g : Fin n → AtomHom dD X Y) :
    finSum n (fun i => add (f i) (g i)) =
      add (finSum n f) (finSum n g) := by
  induction n with
  | zero =>
      simp only [finSum]
      exact (add_zero hD (zero dD X Y)).symm
  | succ n ih =>
      simp only [finSum]
      rw [ih]
      exact add_interchange hD _ _ _ _

theorem finSum_smul {X Y : Atom} {n : ℕ} (r : ℝ)
    (f : Fin n → AtomHom dD X Y) :
    finSum n (fun i => smul r (f i)) = smul r (finSum n f) := by
  induction n with
  | zero =>
      simp only [finSum]
      exact (smul_zero hD r).symm
  | succ n ih =>
      simp only [finSum]
      rw [ih]
      exact (smul_add hD r _ _).symm

theorem finSum_comp {X Y Z : Atom} {n : ℕ}
    (f : Fin n → AtomHom dD X Y) (g : AtomHom dD Y Z) :
    comp (finSum n f) g = finSum n (fun i => comp (f i) g) := by
  induction n with
  | zero =>
      simp only [finSum]
      exact zero_comp hD g
  | succ n ih =>
      simp only [finSum]
      rw [add_comp hD, ih]

theorem comp_finSum {X Y Z : Atom} {n : ℕ}
    (f : AtomHom dD X Y) (g : Fin n → AtomHom dD Y Z) :
    comp f (finSum n g) = finSum n (fun i => comp f (g i)) := by
  induction n with
  | zero =>
      simp only [finSum]
      exact comp_zero hD f
  | succ n ih =>
      simp only [finSum]
      rw [comp_add hD, ih]

theorem finSum_comm {W X : Atom} {m n : ℕ}
    (f : Fin m → Fin n → AtomHom dD W X) :
    finSum m (fun i => finSum n (fun j => f i j)) =
      finSum n (fun j => finSum m (fun i => f i j)) := by
  induction m with
  | zero =>
      simp only [finSum]
      exact (finSum_zero hD n).symm
  | succ m ih =>
      simp only [finSum]
      rw [ih]
      exact (finSum_add hD
        (fun j => finSum m (fun i => f i.castSucc j))
        (fun j => f (Fin.last m) j)).symm

/-- A fixed-order sum supported at one index returns that entry. -/
theorem finSum_single {X Y : Atom} {n : ℕ} (k : Fin n)
    (f : AtomHom dD X Y) :
    finSum n (fun i => if i = k then f else zero dD X Y) = f := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [finSum, Fin.castSucc_ne_last, if_false, if_pos]
        rw [finSum_zero hD, zero_add hD]
      · have hlast : Fin.last n ≠ k.castSucc :=
          (Fin.castSucc_ne_last k).symm
        simp only [finSum, Fin.castSucc_inj, hlast, if_false]
        rw [ih, add_zero hD]

/-- A finite sum of homogeneous atomic morphisms is homogeneous. -/
theorem finSum_memGrade {X Y : Atom} {n : ℕ} {i : ZMod 2}
    (f : Fin n → AtomHom dD X Y) (hf : ∀ k, MemGrade i (f k)) :
    MemGrade i (finSum n f) := by
  induction n with
  | zero => exact zero_memGrade hD i
  | succ n ih =>
      simp only [finSum]
      exact add_memGrade hD _ _
        (ih (f := fun k => f k.castSucc) (fun k => hf k.castSucc))
        (hf (Fin.last n))

end AtomHom

namespace Hom

variable {dD : DData} (hD : DLaws dD)
include hD

/-! ## Entrywise additive and scalar laws -/

theorem add_assoc {X Y : Obj} (f g h : Hom dD X Y) :
    add (add f g) h = add f (add g h) := by
  apply ext
  intro i j
  exact AtomHom.add_assoc hD _ _ _

theorem add_comm {X Y : Obj} (f g : Hom dD X Y) : add f g = add g f := by
  apply ext
  intro i j
  exact AtomHom.add_comm hD _ _

theorem zero_add {X Y : Obj} (f : Hom dD X Y) : add (zero dD X Y) f = f := by
  apply ext
  intro i j
  exact AtomHom.zero_add hD _

theorem add_zero {X Y : Obj} (f : Hom dD X Y) : add f (zero dD X Y) = f := by
  apply ext
  intro i j
  exact AtomHom.add_zero hD _

theorem neg_add {X Y : Obj} (f : Hom dD X Y) :
    add (neg f) f = zero dD X Y := by
  apply ext
  intro i j
  exact AtomHom.neg_add hD _

theorem add_neg {X Y : Obj} (f : Hom dD X Y) :
    add f (neg f) = zero dD X Y := by
  apply ext
  intro i j
  exact AtomHom.add_neg hD _

theorem one_smul {X Y : Obj} (f : Hom dD X Y) : smul 1 f = f := by
  apply ext
  intro i j
  exact AtomHom.one_smul hD _

theorem mul_smul {X Y : Obj} (r s : ℝ) (f : Hom dD X Y) :
    smul (r * s) f = smul r (smul s f) := by
  apply ext
  intro i j
  exact AtomHom.mul_smul hD r s _

theorem add_smul {X Y : Obj} (r s : ℝ) (f : Hom dD X Y) :
    smul (r + s) f = add (smul r f) (smul s f) := by
  apply ext
  intro i j
  exact AtomHom.add_smul hD r s _

theorem smul_add {X Y : Obj} (r : ℝ) (f g : Hom dD X Y) :
    smul r (add f g) = add (smul r f) (smul r g) := by
  apply ext
  intro i j
  exact AtomHom.smul_add hD r _ _

theorem zero_smul {X Y : Obj} (f : Hom dD X Y) :
    smul 0 f = zero dD X Y := by
  apply ext
  intro i j
  exact AtomHom.zero_smul hD _

theorem smul_zero {X Y : Obj} (r : ℝ) :
    smul r (zero dD X Y) = zero dD X Y := by
  apply ext
  intro i j
  exact AtomHom.smul_zero hD r

/-! ## Matrix category laws -/

theorem comp_id {X Y : Obj} (f : Hom dD X Y) : comp f (id dD Y) = f := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size
      (fun j => AtomHom.comp (f i j) (id dD Y j k)) = f i k
  calc
    _ = AtomHom.finSum Y.size (fun j =>
        if j = k then f i k else AtomHom.zero dD (X.atom i) (Y.atom k)) := by
      apply AtomHom.finSum_congr
      intro j
      by_cases hjk : j = k
      · subst j
        simp [id, AtomHom.comp_id hD]
      · simp [id, hjk, AtomHom.comp_zero hD]
    _ = f i k := AtomHom.finSum_single hD k (f i k)

theorem id_comp {X Y : Obj} (f : Hom dD X Y) : comp (id dD X) f = f := by
  apply ext
  intro i k
  change AtomHom.finSum X.size
      (fun j => AtomHom.comp (id dD X i j) (f j k)) = f i k
  calc
    _ = AtomHom.finSum X.size (fun j =>
        if j = i then f i k else AtomHom.zero dD (X.atom i) (Y.atom k)) := by
      apply AtomHom.finSum_congr
      intro j
      by_cases hji : j = i
      · subst j
        simp [id, AtomHom.id_comp hD]
      · have hij : i ≠ j := Ne.symm hji
        simp [id, hji, hij, AtomHom.zero_comp hD]
    _ = f i k := AtomHom.finSum_single hD i (f i k)

theorem zero_comp {X Y Z : Obj} (g : Hom dD Y Z) :
    comp (zero dD X Y) g = zero dD X Z := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size
      (fun j => AtomHom.comp (AtomHom.zero dD _ _) (g j k)) =
    AtomHom.zero dD _ _
  rw [AtomHom.finSum_congr (fun j => AtomHom.zero_comp hD (g j k))]
  exact AtomHom.finSum_zero hD _

theorem comp_zero {X Y Z : Obj} (f : Hom dD X Y) :
    comp f (zero dD Y Z) = zero dD X Z := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size
      (fun j => AtomHom.comp (f i j) (AtomHom.zero dD _ _)) =
    AtomHom.zero dD _ _
  rw [AtomHom.finSum_congr (fun j => AtomHom.comp_zero hD (f i j))]
  exact AtomHom.finSum_zero hD _

theorem comp_assoc {W X Y Z : Obj} (f : Hom dD W X) (g : Hom dD X Y)
    (h : Hom dD Y Z) : comp (comp f g) h = comp f (comp g h) := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size (fun y =>
      AtomHom.comp
        (AtomHom.finSum X.size (fun x => AtomHom.comp (f i x) (g x y)))
        (h y k)) =
    AtomHom.finSum X.size (fun x =>
      AtomHom.comp (f i x)
        (AtomHom.finSum Y.size (fun y => AtomHom.comp (g x y) (h y k))))
  calc
    _ = AtomHom.finSum Y.size (fun y => AtomHom.finSum X.size (fun x =>
        AtomHom.comp (AtomHom.comp (f i x) (g x y)) (h y k))) := by
      apply AtomHom.finSum_congr
      intro y
      exact AtomHom.finSum_comp hD _ _
    _ = AtomHom.finSum Y.size (fun y => AtomHom.finSum X.size (fun x =>
        AtomHom.comp (f i x) (AtomHom.comp (g x y) (h y k)))) := by
      apply AtomHom.finSum_congr
      intro y
      apply AtomHom.finSum_congr
      intro x
      exact AtomHom.comp_assoc hD _ _ _
    _ = AtomHom.finSum X.size (fun x => AtomHom.finSum Y.size (fun y =>
        AtomHom.comp (f i x) (AtomHom.comp (g x y) (h y k)))) :=
      AtomHom.finSum_comm hD _
    _ = _ := by
      apply AtomHom.finSum_congr
      intro x
      exact (AtomHom.comp_finSum hD _ _).symm

/-! ## Matrix bilinearity laws -/

theorem add_comp {X Y Z : Obj} (f g : Hom dD X Y) (h : Hom dD Y Z) :
    comp (add f g) h = add (comp f h) (comp g h) := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size (fun j =>
      AtomHom.comp (AtomHom.add (f i j) (g i j)) (h j k)) =
    AtomHom.add
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (f i j) (h j k)))
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (g i j) (h j k)))
  rw [AtomHom.finSum_congr (fun j => AtomHom.add_comp hD _ _ _),
    AtomHom.finSum_add hD]

theorem comp_add {X Y Z : Obj} (f : Hom dD X Y) (g h : Hom dD Y Z) :
    comp f (add g h) = add (comp f g) (comp f h) := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size (fun j =>
      AtomHom.comp (f i j) (AtomHom.add (g j k) (h j k))) =
    AtomHom.add
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (f i j) (g j k)))
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (f i j) (h j k)))
  rw [AtomHom.finSum_congr (fun j => AtomHom.comp_add hD _ _ _),
    AtomHom.finSum_add hD]

theorem smul_comp {X Y Z : Obj} (r : ℝ) (f : Hom dD X Y) (g : Hom dD Y Z) :
    comp (smul r f) g = smul r (comp f g) := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size (fun j =>
      AtomHom.comp (AtomHom.smul r (f i j)) (g j k)) =
    AtomHom.smul r
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (f i j) (g j k)))
  rw [AtomHom.finSum_congr (fun j => AtomHom.smul_comp hD r _ _),
    AtomHom.finSum_smul hD]

theorem comp_smul {X Y Z : Obj} (r : ℝ) (f : Hom dD X Y) (g : Hom dD Y Z) :
    comp f (smul r g) = smul r (comp f g) := by
  apply ext
  intro i k
  change AtomHom.finSum Y.size (fun j =>
      AtomHom.comp (f i j) (AtomHom.smul r (g j k))) =
    AtomHom.smul r
      (AtomHom.finSum Y.size (fun j => AtomHom.comp (f i j) (g j k)))
  rw [AtomHom.finSum_congr (fun j => AtomHom.comp_smul hD r _ _),
    AtomHom.finSum_smul hD]

/-! ## Matrix grading and decomposition laws -/

theorem zero_memGrade {X Y : Obj} (i : ZMod 2) :
    MemGrade i (zero dD X Y) := by
  intro r s
  exact AtomHom.zero_memGrade hD i

theorem add_memGrade {X Y : Obj} {i : ZMod 2} (f g : Hom dD X Y)
    (hf : MemGrade i f) (hg : MemGrade i g) : MemGrade i (add f g) := by
  intro r s
  exact AtomHom.add_memGrade hD _ _ (hf r s) (hg r s)

theorem neg_memGrade {X Y : Obj} {i : ZMod 2} (f : Hom dD X Y)
    (hf : MemGrade i f) : MemGrade i (neg f) := by
  intro r s
  exact AtomHom.neg_memGrade hD _ (hf r s)

theorem smul_memGrade {X Y : Obj} {i : ZMod 2} (q : ℝ) (f : Hom dD X Y)
    (hf : MemGrade i f) : MemGrade i (smul q f) := by
  intro r s
  exact AtomHom.smul_memGrade hD q _ (hf r s)

theorem component_memGrade {X Y : Obj} (i : ZMod 2) (f : Hom dD X Y) :
    MemGrade i (component i f) := by
  intro r s
  exact AtomHom.component_memGrade hD i _

theorem component_complement {X Y : Obj} (i : ZMod 2) (f : Hom dD X Y) :
    add (component i f) (component (i + 1) f) = f := by
  apply ext
  intro r s
  exact AtomHom.component_complement hD i _

theorem grade_decomposition {X Y : Obj} (f : Hom dD X Y) :
    ∃ f₀ f₁ : Hom dD X Y,
      MemGrade 0 f₀ ∧ MemGrade 1 f₁ ∧ add f₀ f₁ = f := by
  refine ⟨component 0 f, component 1 f,
    component_memGrade hD 0 f, component_memGrade hD 1 f, ?_⟩
  simpa only [_root_.zero_add] using component_complement hD 0 f

theorem grade_disjoint {X Y : Obj} (i : ZMod 2) (f : Hom dD X Y)
    (hf : MemGrade i f) (hf' : MemGrade (i + 1) f) :
    f = zero dD X Y := by
  apply ext
  intro r s
  exact AtomHom.grade_disjoint hD i _ (hf r s) (hf' r s)

theorem id_even (X : Obj) : MemGrade 0 (id dD X) := by
  intro r s
  by_cases hrs : r = s
  · subst s
    simpa [id] using AtomHom.id_even hD (X.atom r)
  · simp [id, hrs]
    exact AtomHom.zero_memGrade hD 0

theorem comp_memGrade {X Y Z : Obj} {i j : ZMod 2}
    (f : Hom dD X Y) (g : Hom dD Y Z)
    (hf : MemGrade i f) (hg : MemGrade j g) :
    MemGrade (i + j) (comp f g) := by
  intro r t
  exact AtomHom.finSum_memGrade hD _ fun s =>
    AtomHom.comp_memGrade hD _ _ (hf r s) (hg s t)

end Hom

end Superfusion.RMod.FromRawDCT
