import MovingProjection.Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Rational realization of Boolean reconfiguration. A clause must already
have a literal at its satisfying endpoint, even when other coordinates are
between their two Boolean values. -/

namespace MovingProjection.ClauseReconfiguration

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Clause (I : Type*) := List (I × Bool)
abbrev Formula (I : Type*) := List (Clause I)

def bit (b : Bool) : ℚ := if b then 1 else 0

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

def corner (a : I → Bool) : I → ℚ := fun i => bit (a i)

def Satisfies (formula : Formula I) (a : I → Bool) : Prop :=
  ∀ clause ∈ formula, ∃ lit ∈ clause, a lit.1 = lit.2

def NoTautologies (formula : Formula I) : Prop :=
  ∀ clause ∈ formula, ∀ i, (i, false) ∈ clause → (i, true) ∉ clause

def Lawful (formula : Formula I) (x : I → ℚ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
  ∀ clause ∈ formula, ∃ lit ∈ clause, x lit.1 = bit lit.2

def Compatible (x : I → ℚ) (a : I → Bool) : Prop :=
  ∀ i b, x i = bit b → a i = b

def Flip (formula : Formula I) (a b : I → Bool) : Prop :=
  Satisfies formula a ∧ Satisfies formula b ∧ ∃ i, ∀ j ≠ i, a j = b j

def SmallStep (formula : Formula I) (ε : ℚ) (x y : I → ℚ) : Prop :=
  Lawful formula x ∧ Lawful formula y ∧ ∀ i, |x i - y i| < ε

abbrev FlipChain (formula : Formula I) := Relation.ReflTransGen (Flip formula)
abbrev MeshChain (formula : Formula I) (ε : ℚ) := Relation.ReflTransGen (SmallStep formula ε)

omit [Fintype I] [DecidableEq I] in
theorem corner_compatible (a : I → Bool) : Compatible (corner a) a :=
  fun _ _ h => bit_injective h

omit [Fintype I] [DecidableEq I] in
theorem corner_lawful {formula : Formula I} {a : I → Bool} (ha : Satisfies formula a) :
    Lawful formula (corner a) := by
  refine ⟨fun i => ?_, fun clause hc => ?_⟩
  · cases h : a i <;> norm_num [corner, bit, h]
  · obtain ⟨lit, hl, he⟩ := ha clause hc
    exact ⟨lit, hl, congrArg bit he⟩

omit [Fintype I] [DecidableEq I] in
theorem compatible_satisfies {formula : Formula I} {x : I → ℚ} {a : I → Bool}
    (hx : Lawful formula x) (ha : Compatible x a) : Satisfies formula a := by
  intro clause hc
  obtain ⟨lit, hl, he⟩ := hx.2 clause hc
  exact ⟨lit, hl, ha lit.1 lit.2 he⟩

theorem compatible_flips {formula : Formula I} {x : I → ℚ} {a b : I → Bool}
    (hx : Lawful formula x) (ha : Compatible x a) (hb : Compatible x b) :
    FlipChain formula a b := by
  let middle (s : Finset I) (i : I) := if i ∈ s then b i else a i
  have hcompat (s : Finset I) : Compatible x (middle s) := by
    intro i value h
    by_cases hi : i ∈ s <;> simp [middle, hi, ha i value h, hb i value h]
  have hreach (s : Finset I) : FlipChain formula a (middle s) := by
    induction s using Finset.induction_on with
    | empty => simpa [middle] using (Relation.ReflTransGen.refl : FlipChain formula a a)
    | @insert i s _ ih =>
      apply ih.tail
      refine ⟨compatible_satisfies hx (hcompat s),
        compatible_satisfies hx (hcompat (insert i s)), i, ?_⟩
      intro j hj
      simp [middle, hj]
  simpa [middle] using hreach Finset.univ

omit [Fintype I] [DecidableEq I] in
theorem common_corner {formula : Formula I} {x y : I → ℚ}
    (h : SmallStep formula 1 x y) : ∃ a, Compatible x a ∧ Compatible y a := by
  let a (i : I) : Bool := decide (x i = 1 ∨ y i = 1)
  refine ⟨a, ?_, ?_⟩
  · intro i b hb
    have hclose := abs_lt.mp (h.2.2 i)
    cases b
    · have hx : x i = 0 := by simpa [bit] using hb
      have hy : y i ≠ 1 := by intro he; rw [hx, he] at hclose; linarith [hclose.1]
      simp [a, hx, hy]
    · have hx : x i = 1 := by simpa [bit] using hb
      simp [a, hx]
  · intro i b hb
    have hclose := abs_lt.mp (h.2.2 i)
    cases b
    · have hy : y i = 0 := by simpa [bit] using hb
      have hx : x i ≠ 1 := by intro he; rw [hy, he] at hclose; linarith [hclose.2]
      simp [a, hy, hx]
    · have hy : y i = 1 := by simpa [bit] using hb
      simp [a, hy]

theorem flips_of_unit_chain {formula : Formula I} {x y : I → ℚ} {a b : I → Bool}
    (hx : Lawful formula x) (ha : Compatible x a) (hb : Compatible y b)
    (h : MeshChain formula 1 x y) : FlipChain formula a b := by
  revert b
  induction h with
  | refl => exact fun hb => compatible_flips hx ha hb
  | @tail u v _ hedge ih =>
    intro b hb
    obtain ⟨c, huc, hvc⟩ := common_corner hedge
    exact (ih huc).trans (compatible_flips hedge.2.1 hvc hb)

private def segment (a b : I → Bool) (t : ℚ) : I → ℚ :=
  fun i => (1 - t) * bit (a i) + t * bit (b i)

omit [Fintype I] in
private theorem segment_lawful {formula : Formula I} {a b : I → Bool}
    (hformula : NoTautologies formula) (h : Flip formula a b)
    {t : ℚ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : Lawful formula (segment a b t) := by
  obtain ⟨ha, hb, pivot, hp⟩ := h
  refine ⟨fun i => ?_, fun cl hc => ?_⟩
  · cases h₁ : a i <;> cases h₂ : b i <;> simp [segment, bit, h₁, h₂, ht₀, ht₁]
  · obtain ⟨⟨i, value⟩, hi, hiv⟩ := ha cl hc
    obtain ⟨⟨j, other⟩, hj, hjv⟩ := hb cl hc
    suffices ∃ lit ∈ cl, a lit.1 = lit.2 ∧ b lit.1 = lit.2 by
      obtain ⟨lit, hl, ha', hb'⟩ := this
      refine ⟨lit, hl, ?_⟩
      simp only [segment, ha', hb']
      ring
    by_cases hi' : i = pivot
    · by_cases hj' : j = pivot
      · subst i j
        have he : value = other := by
          cases value <;> cases other <;> try rfl
          · exact (hformula cl hc pivot hi hj).elim
          · exact (hformula cl hc pivot hj hi).elim
        exact ⟨(pivot, value), hi, hiv, hjv.trans he.symm⟩
      · exact ⟨(j, other), hj, (hp j hj').trans hjv, hjv⟩
    · exact ⟨(i, value), hi, hiv, (hp i hi').symm.trans hiv⟩

omit [Fintype I] [DecidableEq I] in
private theorem segment_dist (a b : I → Bool) (p q : ℚ) (i : I) :
    |segment a b p i - segment a b q i| ≤ |p - q| := by
  cases h₁ : a i <;> cases h₂ : b i <;> simp [segment, bit, h₁, h₂]
  exact le_of_eq (abs_sub_comm _ _)

omit [Fintype I] in
theorem flip_has_mesh {formula : Formula I} {a b : I → Bool}
    (hformula : NoTautologies formula) (h : Flip formula a b)
    {ε : ℚ} (hε : 0 < ε) : MeshChain formula ε (corner a) (corner b) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn₀ : (0 : ℚ) < n := (div_pos one_pos hε).trans hn
  have hsmall : 1 / (n : ℚ) < ε := by
    apply (div_lt_iff₀ hn₀).2
    have h := (div_lt_iff₀ hε).1 hn
    simpa [mul_comm] using h
  let sample (k : ℕ) := segment a b ((k : ℚ) / n)
  have hlegal (k : ℕ) (hk : k ≤ n) : Lawful formula (sample k) :=
    segment_lawful hformula h (div_nonneg (Nat.cast_nonneg _) hn₀.le)
      ((div_le_one hn₀).2 (by exact_mod_cast hk))
  have hchain (k : ℕ) (hk : k ≤ n) : MeshChain formula ε (sample 0) (sample k) := by
    induction k with
    | zero => exact .refl
    | succ k ih =>
      have hk' : k ≤ n := (Nat.le_succ _).trans hk
      refine (ih hk').tail ⟨hlegal k hk', hlegal (k + 1) hk, fun i => ?_⟩
      apply (segment_dist a b _ _ i).trans_lt
      rw [Nat.cast_succ, ← sub_div, show (k : ℚ) - (k + 1) = -1 by ring,
        neg_div, abs_neg, abs_of_nonneg (div_nonneg zero_le_one hn₀.le)]
      exact hsmall
  have hn' : (n : ℚ) ≠ 0 := ne_of_gt hn₀
  have hstart : sample 0 = corner a := by funext i; simp [sample, segment, corner]
  have hfinish : sample n = corner b := by funext i; simp [sample, segment, corner, hn']
  rw [← hstart, ← hfinish]
  exact hchain n le_rfl

theorem fine_iff_flips {formula : Formula I} {a b : I → Bool}
    (hformula : NoTautologies formula) (ha : Satisfies formula a) :
    (∀ ε : ℚ, 0 < ε → MeshChain formula ε (corner a) (corner b)) ↔
      FlipChain formula a b := by
  constructor
  · intro h
    exact flips_of_unit_chain (corner_lawful ha) (corner_compatible a) (corner_compatible b)
      (h 1 zero_lt_one)
  · intro h ε hε
    induction h with
    | refl => exact .refl
    | tail _ hedge ih => exact ih.trans (flip_has_mesh hformula hedge hε)

end MovingProjection.ClauseReconfiguration
