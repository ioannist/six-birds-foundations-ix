import MovingProjection.ClauseReconfiguration

/-! The one-state test language used in the lower bounds. Every comparison
has a singleton on the left and an event of size one or two on the right.
All words have duration two. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

abbrev Word (M : Type*) := M × M

def wordMass {M : Type*} (rate : M → ℚ) (word : Word M) : ℚ :=
  rate word.1 * rate word.2

inductive Test (M : Type*) where
  | equal (left right : Word M)
  | sum (left first second : Word M) (distinct : first ≠ second)

def Test.holds {M : Type*} (query : Test M) (rate : M → ℚ) : Prop :=
  match query with
  | .equal left right => wordMass rate left = wordMass rate right
  | .sum left first second _ =>
    wordMass rate left = wordMass rate first + wordMass rate second

variable {M I : Type*} [Fintype M]

def Lawful (tests : List (Test M)) (floor : ℚ) (rate : M → ℚ) : Prop :=
  (∑ m, rate m) = 1 ∧ (∀ m, floor ≤ rate m) ∧ ∀ test ∈ tests, test.holds rate

def SmallStep (tests : List (Test M)) (floor ε : ℚ) (a b : M → ℚ) : Prop :=
  Lawful tests floor a ∧ Lawful tests floor b ∧ ∀ m, |a m - b m| < ε

abbrev Chain (tests : List (Test M)) (floor ε : ℚ) :=
  Relation.ReflTransGen (SmallStep tests floor ε)

def Fine (tests : List (Test M)) (floor : ℚ) (a b : M → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → Chain tests floor ε a b

omit [Fintype M] in
theorem padded_add_iff {rate : M → ℚ} {z a b ref : M} (hab : a ≠ b)
    (href : rate ref ≠ 0) :
    (Test.sum (z, ref) (a, ref) (b, ref) (fun h => hab (congrArg Prod.fst h))).holds rate ↔
      rate z = rate a + rate b := by
  change rate z * rate ref = rate a * rate ref + rate b * rate ref ↔ _
  rw [← add_mul, mul_left_inj' href]

omit [Fintype M] in
theorem product_iff {rate : M → ℚ} {z a b ref : M} (href : rate ref ≠ 0) :
    (Test.equal (z, ref) (a, b)).holds rate ↔ rate z = rate a * rate b / rate ref :=
  (eq_div_iff href).symm

def literalRate (scale : ℚ) (x : I → ℚ) (lit : I × Bool) : ℚ :=
  if lit.2 then scale * (3 - 2 * x lit.1) else scale * (1 + 2 * x lit.1)

omit [Fintype M] in
theorem literalRate_eq_scale_iff {scale : ℚ} (hscale : scale ≠ 0)
    (x : I → ℚ) (lit : I × Bool) :
    literalRate scale x lit = scale ↔ x lit.1 = ClauseReconfiguration.bit lit.2 := by
  obtain ⟨i, value⟩ := lit
  have cancel (v : ℚ) : scale * v = scale ↔ v = 1 := by
    constructor
    · intro h
      apply (mul_right_inj' hscale).mp
      simpa only [mul_one] using h
    · intro h
      simp [h]
  cases value
  · simp [literalRate, ClauseReconfiguration.bit, cancel]
  · simp [literalRate, ClauseReconfiguration.bit, cancel]
    constructor <;> (intro h; linarith)

omit [Fintype M] in
theorem clause_product_iff {scale : ℚ} (hscale : scale ≠ 0)
    (x : I → ℚ) (clause : ClauseReconfiguration.Clause I) :
    (clause.map fun lit => literalRate scale x lit - scale).prod = 0 ↔
      ∃ lit ∈ clause, x lit.1 = ClauseReconfiguration.bit lit.2 := by
  induction clause with
  | nil => simp
  | cons lit rest ih =>
    simp only [List.map_cons, List.prod_cons, mul_eq_zero, sub_eq_zero, ih,
      literalRate_eq_scale_iff hscale, List.mem_cons]
    constructor
    · rintro (h | ⟨other, ho, he⟩)
      · exact ⟨lit, Or.inl rfl, h⟩
      · exact ⟨other, Or.inr ho, he⟩
    · rintro ⟨other, (rfl | ho), he⟩
      · exact Or.inl he
      · exact Or.inr ⟨other, ho, he⟩

def readCube (selected : I → M) (scale : ℚ) (rate : M → ℚ) : I → ℚ :=
  fun i => (rate (selected i) / scale - 1) / 2

/-- The leaf rates alone recover a Boolean chain from an event chain.
The `hread` premise is the correctness of the compiled clause equations. -/
theorem flips_of_event_chain [Fintype I] [DecidableEq I]
    {formula : ClauseReconfiguration.Formula I} {tests : List (Test M)}
    {scale : ℚ} (hscale : 0 < scale) (selected : I → M)
    (hread : ∀ rate, Lawful tests scale rate →
      ClauseReconfiguration.Lawful formula (readCube selected scale rate))
    {a b : M → ℚ} (ha : Lawful tests scale a) {u v : I → Bool}
    (hu : readCube selected scale a = ClauseReconfiguration.corner u)
    (hv : readCube selected scale b = ClauseReconfiguration.corner v)
    (h : Chain tests scale (2 * scale) a b) : ClauseReconfiguration.FlipChain formula u v := by
  apply ClauseReconfiguration.flips_of_unit_chain (hread a ha)
    (hu ▸ ClauseReconfiguration.corner_compatible u)
    (hv ▸ ClauseReconfiguration.corner_compatible v)
  refine h.lift (readCube selected scale) (fun p q hpq => ⟨hread p hpq.1, hread q hpq.2.1, ?_⟩)
  intro i
  have hdiff : readCube selected scale p i - readCube selected scale q i =
      (p (selected i) - q (selected i)) / (2 * scale) := by
    unfold readCube
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos (by positivity : 0 < 2 * scale)]
  exact (div_lt_one (by positivity : 0 < 2 * scale)).2 (hpq.2.2 (selected i))

/-- Rational lifts with a uniform coordinate bound on their rate change
carry arbitrary Boolean meshes to arbitrary event meshes. Polynomials on a
closed cube have such a bound, as used in the paper proof. -/
theorem event_fine_of_flips [Fintype I] [DecidableEq I]
    {formula : ClauseReconfiguration.Formula I} (hformula : ClauseReconfiguration.NoTautologies formula)
    {tests : List (Test M)} {floor : ℚ} (lift : (I → ℚ) → M → ℚ)
    (hlawful : ∀ x, ClauseReconfiguration.Lawful formula x → Lawful tests floor (lift x))
    {bound : ℚ} (hbound : 0 < bound)
    (hmesh : ∀ {x y τ}, 0 < τ → ClauseReconfiguration.SmallStep formula τ x y →
      ∀ m, |lift x m - lift y m| < bound * τ)
    {u v : I → Bool} (h : ClauseReconfiguration.FlipChain formula u v) :
    Fine tests floor (lift (ClauseReconfiguration.corner u)) (lift (ClauseReconfiguration.corner v)) := by
  intro ε hε
  have hτ : 0 < ε / bound := div_pos hε hbound
  have hchain : ClauseReconfiguration.MeshChain formula (ε / bound)
      (ClauseReconfiguration.corner u) (ClauseReconfiguration.corner v) := by
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.trans (ClauseReconfiguration.flip_has_mesh hformula hstep hτ)
  refine hchain.lift lift (fun x y hxy => ⟨hlawful x hxy.1, hlawful y hxy.2.1, fun m => ?_⟩)
  have hsize : bound * (ε / bound) = ε := by field_simp
  simpa [hsize] using hmesh hτ hxy m

end MovingProjection.OneStateEvents
