import MovingProjection.CalibratedResponses

/-! Ordinary singleton comparisons copy bounded monomials into selected
response coordinates. A reserved coordinate leaves an exact budget for
their sum. The only additive comparison is the duration-one control. -/

namespace MovingProjection.ResponseBudgets

open scoped BigOperators
open CalibratedResponses

set_option synthInstance.maxSize 512

variable {J T X : Type*} [Fintype J] [Fintype T] [Fintype X]
  [DecidableEq J] [DecidableEq T] [DecidableEq X] [Nonempty X]

structure Rows (J T : Type*) where
  weight : T → J → ℚ
  weight_nonneg : ∀ v j, 0 ≤ weight v j
  power : T → J → ℕ
  complementPower : T → J → ℕ
  totalDegree : ∀ v j, power v j + complementPower v j ≤ 2
  bound : T → ℚ
  bound_nonneg : ∀ v, 0 ≤ bound v

abbrev Row (J T : Type*) := (J × Bool) ⊕ T
abbrev Probe (J : Type*) := Option J
abbrev Aux (J T : Type*) := Unit ⊕ (J ⊕ (Row J T ⊕ (Row J T × J)))
abbrev M (J T : Type*) := Mark (Aux J T)

-- Reuse the canonical sum/product deciders without a deep instance search.
private abbrev rowDecidableEq : DecidableEq (Row J T) :=
  @instDecidableEqSum _ _ inferInstance inferInstance

abbrev auxDecidableEq : DecidableEq (Aux J T) :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance
      (@instDecidableEqSum _ _ rowDecidableEq
        (@instDecidableEqProd _ _ rowDecidableEq inferInstance)))

attribute [local instance] auxDecidableEq

abbrev G (J T : Type*) := Row J T × J
abbrev D (J T : Type*) := Unit ⊕ (Probe J ⊕ ((J × Probe J) ⊕ (Row J T ⊕ (G J T × Probe J))))

variable (P : Rows J T)

def coeff : Row J T → J → ℚ
  | .inl (j, _), i => if i = j then 1 else 0
  | .inr v, i => P.weight v i

def bound : Row J T → ℚ
  | .inl _ => 1
  | .inr v => P.bound v

def power : Row J T → J → ℕ
  | .inl (_, b), _ => if b then 0 else 1
  | .inr v, i => P.power v i

def compPower : Row J T → J → ℕ
  | .inl (_, b), _ => if b then 1 else 0
  | .inr v, i => P.complementPower v i

def degree (v : Row J T) (i : J) : ℕ := power P v i + compPower P v i

def amplitude (J : Type*) [Fintype J] : ℚ :=
  1 / (4 * (Fintype.card (Probe J) : ℚ))

omit [DecidableEq J] in
theorem amplitude_pos : 0 < amplitude J := by
  unfold amplitude
  rw [Fintype.card_option, Nat.cast_succ]
  positivity

omit [DecidableEq J] in
theorem amplitude_sum : (Fintype.card (Probe J) : ℚ) * amplitude J = 1/4 := by
  unfold amplitude
  have hn : (Fintype.card (Probe J) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

def scale (v : Row J T) : ℚ := 1 / (2 * (1 + bound P v + ∑ i, coeff P v i))

def pad : Other (Aux J T) := .inr (.inl ())
def selector (i : J) : Other (Aux J T) := .inr (.inr (.inl i))
def load (v : Row J T) : Other (Aux J T) := .inr (.inr (.inr (.inl v)))
def coefficient (v : Row J T) (i : J) : Other (Aux J T) := .inr (.inr (.inr (.inr (v,i))))

def pair (g : G J T) : TimedPair (Other (Aux J T)) 4 where
  first := selector g.2
  next := selector g.2
  tail := load g.1 :: List.replicate (degree P g.1 g.2) pad
  other := coefficient g.1 g.2 :: (List.replicate (power P g.1 g.2) (.inl false) ++
    List.replicate (compPower P g.1 g.2) (.inl true))
  duration := by simp [degree]
  fits := by
    have hh : degree P g.1 g.2 ≤ 2 := by
      rcases g.1 with (⟨j,b⟩ | v)
      · cases b <;> simp [degree, power, compPower]
      · exact P.totalDegree v g.2
    simp only [List.length_cons, List.length_replicate]
    omega

def calibration : D J T → (Other (Aux J T) × Probe J) × ℚ
  | .inl _ => ((.inl false,none), amplitude J)
  | .inr (.inl j) => ((pad,j), amplitude J)
  | .inr (.inr (.inl (i,j))) => ((selector i,j), if j = some i then amplitude J else 0)
  | .inr (.inr (.inr (.inl v))) => ((load v,none), 1/2 - scale P v * bound P v)
  | .inr (.inr (.inr (.inr ((v,i),j)))) =>
    ((coefficient v i,j), if j = some i then scale P v * coeff P v i else 0)

def catalogue : Catalogue (Aux J T) (Probe J) (G J T) (D J T) :=
  ⟨3, pair P, calibration P, amplitude J⟩

def term (t : J → ℚ) (v : Row J T) (j : J) : ℚ :=
  coeff P v j * t j ^ power P v j * (1 - t j) ^ compPower P v j

def Solution (t : J → ℚ) : Prop :=
  (∀ j, 0 ≤ t j ∧ t j ≤ 1) ∧ ∀ v, (∑ j, term P t (.inr v) j) ≤ P.bound v

def assign (t : J → ℚ) : M J T × Probe J → ℚ
  | (.inl _, _) => amplitude J/2
  | (.inr (.inl false),none) => amplitude J
  | (.inr (.inl true),none) => 0
  | (.inr (.inl b),some j) => amplitude J * (if b then 1 - t j else t j)
  | (.inr (.inr (.inl _)),_) => amplitude J
  | (.inr (.inr (.inr (.inl i))),j) => if j = some i then amplitude J else 0
  | (.inr (.inr (.inr (.inr (.inl v)))),none) => 1/2 - scale P v * bound P v
  | (.inr (.inr (.inr (.inr (.inl v)))),some i) => scale P v * term P t v i
  | (.inr (.inr (.inr (.inr (.inr (v,i))))),j) =>
    if j = some i then scale P v * coeff P v i else 0

omit [Fintype J] [Fintype T] [DecidableEq T] in
private theorem coeff_nonneg (v : Row J T) (j : J) : 0 ≤ coeff P v j := by
  rcases v with (⟨i,b⟩ | v)
  · by_cases hi : j = i <;> simp [coeff, hi]
  · exact P.weight_nonneg v j

omit [Fintype J] [Fintype T] [DecidableEq J] [DecidableEq T] in
private theorem bound_nonneg (v : Row J T) : 0 ≤ bound P v := by
  rcases v with (_ | v)
  · exact zero_le_one
  · exact P.bound_nonneg v

omit [Fintype T] [DecidableEq T] in
private theorem scale_pos (v : Row J T) : 0 < scale P v := by
  unfold scale
  have h : 0 ≤ ∑ i, coeff P v i := Finset.sum_nonneg (fun i _ => coeff_nonneg P v i)
  have hb := bound_nonneg P v
  positivity

omit [Fintype T] [DecidableEq T] in
private theorem scaled_bound_le (v : Row J T) : scale P v * bound P v ≤ 1/2 := by
  have h : 0 ≤ ∑ i, coeff P v i := Finset.sum_nonneg (fun i _ => coeff_nonneg P v i)
  have hk : 0 < 2 * (1 + bound P v + ∑ i, coeff P v i) := by
    have := bound_nonneg P v
    positivity
  unfold scale
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hk]
  linarith

omit [Fintype T] [DecidableEq T] in
private theorem scaled_coeff_le (v : Row J T) (j : J) : scale P v * coeff P v j ≤ 1/2 := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset J)) (f := coeff P v)
    (fun i _ => coeff_nonneg P v i) (Finset.mem_univ j)
  have hb := bound_nonneg P v
  have hk : 0 < 2 * (1 + bound P v + ∑ i, coeff P v i) := by
    have hsum : 0 ≤ ∑ i, coeff P v i := Finset.sum_nonneg (fun i _ => coeff_nonneg P v i)
    positivity
  unfold scale
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hk]
  linarith

omit [Fintype J] [Fintype T] [DecidableEq T] in
private theorem term_nonneg {t : J → ℚ} (ht : ∀ j, 0 ≤ t j ∧ t j ≤ 1)
    (v : Row J T) (j : J) : 0 ≤ term P t v j := by
  unfold term
  have h := coeff_nonneg P v j
  have h0 := (ht j).1
  have h1 := sub_nonneg.mpr (ht j).2
  positivity

omit [Fintype T] [DecidableEq T] in
private theorem box_row (t : J → ℚ) (i : J) (b : Bool) :
    (∑ j, |term P t (.inl (i,b)) j|) = if b then |1 - t i| else |t i| := by
  have hh (j : J) : |term P t (.inl (i,b)) j| =
      if j = i then (if b then |1 - t i| else |t i|) else 0 := by
    by_cases hj : j = i
    · subst j
      cases b <;> simp [term, coeff, power, compPower]
    · simp [term, coeff, hj]
  simp only [hh, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype T] [DecidableEq T] in
private theorem all_rows {t : J → ℚ} (ht : Solution P t) (v : Row J T) :
    (∑ j, |term P t v j|) ≤ bound P v := by
  rcases v with (⟨i,b⟩ | v)
  · rw [box_row]
    obtain ⟨h₀,h₁⟩ := ht.1 i
    cases b
    · simpa [bound, abs_of_nonneg h₀] using h₁
    · simp only [if_true, bound, abs_of_nonneg (sub_nonneg.mpr h₁)]
      linarith
  · simp only [abs_of_nonneg (term_nonneg P ht.1 _ _)]
    exact ht.2 v

omit [Fintype J] [Fintype T] [DecidableEq J] [DecidableEq T] in
private theorem read_pair {x : M J T × Probe J → ℚ} (v : Row J T) (i : J) (j : Probe J) :
    response ((pair P (v,i)).left) x j =
      x (.inr (selector i), j) * (x (.inr (load v),j) * x (.inr pad,j) ^ degree P v i) := by
  simp [pair, response, TimedPair.left, List.map_replicate, List.prod_replicate]

omit [Fintype J] [Fintype T] [DecidableEq J] [DecidableEq T] in
private theorem read_other {x : M J T × Probe J → ℚ} (v : Row J T) (i : J) (j : Probe J) :
    response ((pair P (v,i)).right) x j =
      x (.inr (selector i),j) * (x (.inr (coefficient v i),j) *
        (x (toggle false,j)^power P v i * x (toggle true,j)^compPower P v i)) := by
  simp [pair, response, TimedPair.right, List.map_replicate, List.prod_replicate, toggle]

omit [Fintype T] [DecidableEq T] in
private theorem cal_assign (t : J → ℚ) (e : D J T) :
    assign P t (.inr (calibration P e).1.1,(calibration P e).1.2) = (calibration P e).2 := by
  rcases e with (u | j | ⟨i,j⟩ | v | ⟨⟨v,i⟩,j⟩) <;> rfl

omit [Fintype T] [DecidableEq T] in
theorem assign_lawful {t : J → ℚ} (ht : Solution P t) :
    (catalogue P).Lawful (assign P t) := by
  refine ⟨?_, fun _ => rfl, cal_assign P t, ?_, ?_⟩
  · intro m
    have hk := amplitude_pos (J := J)
    have hs := amplitude_sum (J := J)
    rcases m with (u | b | u | i | v | ⟨v,i⟩)
    · simp only [assign, abs_of_nonneg (by positivity : 0 ≤ amplitude J / 2),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith
    · calc
        _ ≤ ∑ j : Probe J, amplitude J := by
          apply Finset.sum_le_sum
          intro j _
          cases j with
          | none => cases b <;> simp [assign, abs_of_pos hk, hk.le]
          | some j =>
            have h₀ := (ht.1 j).1
            have h₁ := (ht.1 j).2
            cases b
            · simpa [assign, abs_of_nonneg (mul_nonneg hk.le h₀)] using
                (mul_le_mul_of_nonneg_left h₁ hk.le)
            · simpa [assign, abs_of_nonneg (mul_nonneg hk.le (sub_nonneg.mpr h₁))] using
                (mul_le_mul_of_nonneg_left (show 1-t j ≤ 1 by linarith) hk.le)
        _ ≤ _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]; norm_num
    · simp only [assign, abs_of_pos hk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
      norm_num
    · have hk' : amplitude J ≤ 1/2 := by
        have hn : (1 : ℚ) ≤ Fintype.card (Probe J) := by
          exact_mod_cast Fintype.card_pos (α := Probe J)
        nlinarith
      simpa only [assign, abs_ite, abs_zero, abs_of_pos hk,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using hk'
    · rw [Fintype.sum_option]
      simp only [assign, abs_of_nonneg (sub_nonneg.mpr (scaled_bound_le P v)), abs_mul,
        abs_of_pos (scale_pos P v), ← Finset.mul_sum]
      have h := mul_le_mul_of_nonneg_left (all_rows P ht v) (scale_pos P v).le
      linarith
    · have h := mul_nonneg (scale_pos P v).le (coeff_nonneg P v i)
      simpa only [assign, abs_ite, abs_zero, abs_of_nonneg h,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using scaled_coeff_le P v i
  · intro j
    cases j
    · simp [catalogue, assign, toggle]
    · simp [catalogue, assign, toggle]
      ring
  · rintro ⟨v,i⟩ j
    change response ((pair P (v,i)).left) (assign P t) j =
      response ((pair P (v,i)).right) (assign P t) j
    rw [read_pair, read_other]
    by_cases hj : j = some i
    · subst j
      simp only [assign, selector, load, pad, coefficient, toggle, if_true, if_false, Bool.false_eq_true]
      unfold term degree
      rw [mul_pow, mul_pow, pow_add]
      ring
    · simp [assign, selector, hj]

variable {P} {B : ParityBasis (Probe J) X}

abbrev Native (P : Rows J T) (B : ParityBasis (Probe J) X) := State (catalogue P) B

def decode (s : Native P B) (j : J) : ℚ := s.val.law.spectrum (toggle false,some j) / amplitude J

private theorem decoded_comparison (s : Native P B) (hp : s.val.profile = profile)
    (v : Row J T) (i : J) :
    s.val.law.spectrum (.inr (load v),some i) = scale P v * term P (decode s) v i := by
  let x := s.val.law.spectrum
  have hx := lawful_state s hp
  have he := hx.comparisons (v,i) (some i)
  change response ((pair P (v,i)).left) x (some i) = response ((pair P (v,i)).right) x (some i) at he
  rw [read_pair, read_other] at he
  have hk := amplitude_pos (J := J)
  have hs : x (.inr (selector i),some i) = amplitude J :=
    by simpa [catalogue, calibration] using hx.calibrations (.inr (.inr (.inl (i,some i))))
  have hf : x (.inr (pad : Other (Aux J T)),some i) = amplitude J :=
    hx.calibrations (.inr (.inl (some i)))
  have hc : x (.inr (coefficient v i),some i) = scale P v * coeff P v i :=
    by simpa [catalogue, calibration] using
      hx.calibrations (.inr (.inr (.inr (.inr ((v,i),some i)))))
  rw [hs, hf, hc] at he
  have ha : x (toggle false,some i) = amplitude J * decode s i := by
    change x (toggle false,some i) = amplitude J * (x (toggle false,some i) / amplitude J)
    field_simp
  have hb : x (toggle true,some i) = amplitude J * (1 - decode s i) := by
    have hh : x (toggle false,some i) + x (toggle true,some i) = amplitude J :=
      hx.complement (some i)
    rw [mul_sub, mul_one, ← ha]
    linarith
  apply mul_right_cancel₀ (pow_ne_zero (degree P v i) hk.ne')
  have h := mul_left_cancel₀ hk.ne' he
  rw [ha, hb, mul_pow, mul_pow] at h
  rw [h, degree, pow_add]
  unfold term
  ring

private theorem decoded_budget (s : Native P B) (hp : s.val.profile = profile) (v : Row J T) :
    (∑ i, |term P (decode s) v i|) ≤ bound P v := by
  have hx := lawful_state s hp
  have hr : s.val.law.spectrum (.inr (load v),none) = 1/2 - scale P v * bound P v :=
    hx.calibrations (.inr (.inr (.inr (.inl v))))
  have hb := hx.budget (.inr (load v))
  rw [Fintype.sum_option, hr, abs_of_nonneg (sub_nonneg.mpr (scaled_bound_le P v))] at hb
  simp only [decoded_comparison s hp v, abs_mul, abs_of_pos (scale_pos P v), ← Finset.mul_sum] at hb
  apply le_of_mul_le_mul_left _ (scale_pos P v)
  linarith

theorem decode_solution (s : Native P B) (hp : s.val.profile = profile) : Solution P (decode s) := by
  refine ⟨fun i => ?_, fun v => ?_⟩
  · have h₀ := decoded_budget s hp (.inl (i,false))
    have h₁ := decoded_budget s hp (.inl (i,true))
    rw [box_row] at h₀ h₁
    change |decode s i| ≤ 1 at h₀
    change |1 - decode s i| ≤ 1 at h₁
    constructor <;> linarith [(abs_le.mp h₀).2, (abs_le.mp h₁).2]
  · exact (Finset.sum_le_sum (fun i _ => le_abs_self (term P (decode s) (.inr v) i))).trans
      (decoded_budget s hp (.inr v))

noncomputable def lift (B : ParityBasis (Probe J) X) (t : J → ℚ) (ht : Solution P t) :
    Native P B :=
  build B (assign P t) (assign_lawful P ht)

theorem decode_lift (t : J → ℚ) (ht : Solution P t) : decode (lift B t ht) = t := by
  funext i
  change (amplitude J * t i) / amplitude J = t i
  exact mul_div_cancel_left₀ _ (amplitude_pos (J := J)).ne'

/-- Rational chains of solutions in the unit box. -/
def BoxStep (η : ℚ) (t u : J → ℚ) : Prop :=
  Solution P t ∧ Solution P u ∧ ∀ j, |t j - u j| < η

abbrev BoxChain (η : ℚ) := Relation.ReflTransGen (BoxStep (P := P) η)

private theorem power_change {x y : ℚ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) (d : ℕ) :
    |x^d - y^d| ≤ |x-y| * d := by
  have hb : max |x| |y| ≤ 1 := by rw [abs_of_nonneg hx₀, abs_of_nonneg hy₀]; exact max_le hx₁ hy₁
  have hn : 0 ≤ max |x| |y| := (abs_nonneg x).trans (le_max_left _ _)
  exact (abs_pow_sub_pow_le x y d).trans
    (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hn hb))

omit [Fintype J] [Fintype T] [DecidableEq J] [DecidableEq T] in
private theorem degree_le (v : Row J T) (j : J) : degree P v j ≤ 2 := by
  rcases v with (⟨i,b⟩ | v)
  · cases b <;> simp [degree, power, compPower]
  · exact P.totalDegree v j

omit [Fintype T] [DecidableEq T] in
private theorem scaled_term_change {t u : J → ℚ} (ht : Solution P t) (hu : Solution P u)
    (v : Row J T) (j : J) :
    |scale P v * term P t v j - scale P v * term P u v j| ≤ |t j - u j| := by
  let d := power P v j
  let e := compPower P v j
  let a := t j ^ d
  let b := u j ^ d
  let c := (1-t j)^e
  let f := (1-u j)^e
  let w := scale P v * coeff P v j
  have hw : 0 ≤ w := mul_nonneg (scale_pos P v).le (coeff_nonneg P v j)
  have hw' : w ≤ 1/2 := scaled_coeff_le P v j
  have hb : |b| ≤ 1 := by
    dsimp [b]
    rw [abs_of_nonneg (pow_nonneg (hu.1 j).1 _)]
    exact pow_le_one₀ (hu.1 j).1 (hu.1 j).2
  have hc : |c| ≤ 1 := by
    dsimp [c]
    rw [abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (ht.1 j).2) _)]
    exact pow_le_one₀ (sub_nonneg.mpr (ht.1 j).2) (by linarith [(ht.1 j).1])
  have h₀ : |a-b| ≤ |t j-u j| * d :=
    power_change (ht.1 j).1 (ht.1 j).2 (hu.1 j).1 (hu.1 j).2 d
  have h₁ : |c-f| ≤ |t j-u j| * e := by
    have h := power_change (sub_nonneg.mpr (ht.1 j).2) (show 1-t j ≤ 1 by linarith [(ht.1 j).1])
      (sub_nonneg.mpr (hu.1 j).2) (show 1-u j ≤ 1 by linarith [(hu.1 j).1]) e
    rwa [show 1-t j-(1-u j)=u j-t j by ring, abs_sub_comm (u j)] at h
  have hab : |a*c-b*f| ≤ |t j-u j| * ((d : ℚ) + e) := by
    rw [show a*c-b*f=(a-b)*c+b*(c-f) by ring, mul_add]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hc).trans h₀)
      ((mul_le_of_le_one_left (abs_nonneg _) hb).trans h₁)
  have hd : (d : ℚ) + e ≤ 2 := by exact_mod_cast degree_le (P := P) v j
  have hdeg : 0 ≤ (d : ℚ) + e := by positivity
  have hunit : w * ((d : ℚ) + e) ≤ 1 := by
    calc
      _ ≤ (1/2) * ((d : ℚ) + e) := mul_le_mul_of_nonneg_right hw' hdeg
      _ ≤ _ := by linarith
  rw [show scale P v * term P t v j - scale P v * term P u v j = w * (a*c-b*f) by
    dsimp [term, w, a, b, c, f, d, e]
    ring, abs_mul, abs_of_nonneg hw]
  calc
    _ ≤ w * (|t j-u j| * ((d : ℚ) + e)) := mul_le_mul_of_nonneg_left hab hw
    _ = |t j-u j| * (w * ((d : ℚ) + e)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (abs_nonneg _) hunit

omit [DecidableEq J] in
private theorem amplitude_le_one : amplitude J ≤ 1 := by
  have h := amplitude_sum (J := J)
  have hn : (1 : ℚ) ≤ Fintype.card (Probe J) := by exact_mod_cast Fintype.card_pos (α := Probe J)
  nlinarith [amplitude_pos (J := J)]

omit [Fintype T] [DecidableEq T] in
private theorem assign_near {t u : J → ℚ} {η : ℚ} (ht : Solution P t) (hu : Solution P u)
    (h : ∀ j, |t j - u j| < η) (hη : 0 < η) (mj : M J T × Probe J) :
    |assign P t mj - assign P u mj| < η := by
  rcases mj with ⟨m,j⟩
  rcases m with (_ | b | _ | i | v | ⟨v,i⟩)
  · simpa only [assign, sub_self, abs_zero] using hη
  · cases j with
    | none => cases b <;> simpa only [assign, sub_self, abs_zero] using hη
    | some j =>
      have hb (x y : ℚ) (hd : |x-y| < η) :
          |amplitude J * x - amplitude J * y| < η := by
        rw [← mul_sub, abs_mul, abs_of_pos (amplitude_pos (J := J))]
        exact (mul_le_of_le_one_left (abs_nonneg _) amplitude_le_one).trans_lt hd
      cases b
      · exact hb (t j) (u j) (h j)
      · apply hb (1-t j) (1-u j)
        rw [show (1-t j)-(1-u j)=u j-t j by ring, abs_sub_comm]
        exact h j
  · simpa only [assign, sub_self, abs_zero] using hη
  · simpa only [assign, sub_self, abs_zero] using hη
  · cases j with
    | none => simpa only [assign, sub_self, abs_zero] using hη
    | some j => exact (scaled_term_change ht hu v j).trans_lt (h j)
  · simpa only [assign, sub_self, abs_zero] using hη

def boxMesh (J : Type*) [Fintype J] (ε : ℚ) := ε / ((Fintype.card (Probe J) : ℚ)+1)

omit [DecidableEq J] in
private theorem boxMesh_pos {ε : ℚ} (hε : 0 < ε) : 0 < boxMesh J ε := by unfold boxMesh; positivity

private theorem lift_step {t u : J → ℚ} {ε : ℚ} (hε : 0 < ε)
    (h : BoxStep (P := P) (boxMesh J ε) t u) :
    (instrument (catalogue P) B).Step ε (lift B t h.1) (lift B u h.2.1) := by
  refine Or.inl ⟨rfl, ?_⟩
  rintro m ⟨x,v⟩ ⟨y,w⟩
  let a := fun j => assign P t (m,j)
  let c := fun j => assign P u (m,j)
  change |rate m * B.kernel a x y * 1 - rate m * B.kernel c x y * 1| < ε
  have hr (q : M J T) : 0 ≤ rate q := (floor_pos (M := Aux J T)).le.trans (floor_le_rate q)
  have hr' : rate m ≤ 1 := by
    rw [← rate_sum (M := Aux J T)]
    exact Finset.single_le_sum (fun q _ => hr q) (Finset.mem_univ m)
  rw [mul_one, mul_one, ← mul_sub, abs_mul, abs_of_nonneg (hr m)]
  have hk := B.kernel_sub_le (fun j => (assign_near h.1 h.2.1 h.2.2 (boxMesh_pos hε) (m,j)).le) x y
  refine ((mul_le_of_le_one_left (abs_nonneg _) hr').trans hk).trans_lt ?_
  have he : ((Fintype.card (Probe J) : ℚ) + 1) * boxMesh J ε = ε := by
    unfold boxMesh
    have hn : (Fintype.card (Probe J) : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  linarith [boxMesh_pos (J := J) hε]

theorem lift_chain {t u : J → ℚ} (ht : Solution P t) (hu : Solution P u)
    {ε : ℚ} (hε : 0 < ε) (h : BoxChain (P := P) (boxMesh J ε) t u) :
    (instrument (catalogue P) B).Chain ε (lift B t ht) (lift B u hu) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact (ih hs.1).tail (lift_step hε hs)

def nativeMesh (J T X : Type*) [Fintype J] [Fintype T] [Fintype X] (η : ℚ) :=
  floor (Aux J T) * (amplitude J * η) / (2 * (Fintype.card (X × Unit) : ℚ) + 1)

omit [DecidableEq J] [DecidableEq T] [DecidableEq X] in
private theorem nativeMesh_pos {η : ℚ} (hη : 0 < η) : 0 < nativeMesh J T X η := by
  unfold nativeMesh
  have := floor_pos (M := Aux J T)
  have := amplitude_pos (J := J)
  positivity

private theorem decode_step {s t : Native P B} (hs : s.val.profile = profile)
    (ht : t.val.profile = profile) {η : ℚ} (hη : 0 < η)
    (h : (instrument (catalogue P) B).Step (nativeMesh J T X η) s t) :
    BoxStep (P := P) η (decode s) (decode t) := by
  have hn := ((instrument (catalogue P) B).step_iff_near_of_profile_eq (hs.trans ht.symm)).mp h
  let D := (instrument (catalogue P) B).base.protocol
  have ht' : D.legal s.val.profile t.val.law := by rw [hs, ← ht]; exact t.val.legal
  have hk := amplitude_pos (J := J)
  have hl := spectralModulus_for_physicalStep (R := Unit) B
    (floor_pos (M := Aux J T)) (show (1/2 : ℚ) < 1 by norm_num) (mul_pos hk hη)
    (p := D.fiber s.val.profile) (ν := D.ν) (rev := D.reverse)
    ⟨s.val.legal.2.2, ht'.2.2, hn⟩
  refine ⟨decode_solution s hs, decode_solution t ht, fun j => ?_⟩
  unfold decode
  rw [← sub_div, abs_div, abs_of_pos hk]
  exact (div_lt_iff₀ hk).mpr (by simpa only [mul_comm] using hl.2.2 (toggle false,some j))

theorem decode_chain {s t : Native P B} (hs : s.val.profile = profile)
    (ht : t.val.profile = profile) {η : ℚ} (hη : 0 < η)
    (h : (instrument (catalogue P) B).Chain (nativeMesh J T X η) s t) :
    BoxChain (P := P) η (decode s) (decode t) := by
  induction h with
  | refl => exact .refl
  | @tail u v hu hedge ih =>
    have huv : u.val.profile = profile := le_antisymm
      (ht ▸ hedge.profile_le) (hs ▸ EventExperiments.Chain.profile_le hu)
    exact (ih huv).tail (decode_step huv ht hη hedge)

/-- Fine reachability equivalence for the actual one-licence instrument. -/
theorem fine_iff_box {t u : J → ℚ} (ht : Solution P t) (hu : Solution P u) :
    (instrument (catalogue P) B).Factorable (lift B t ht) (lift B u hu) ↔
      ∀ η : ℚ, 0 < η → BoxChain (P := P) η t u := by
  constructor
  · intro h η hη
    simpa only [decode_lift] using decode_chain rfl rfl hη (h _ (nativeMesh_pos hη))
  · intro h ε hε
    exact lift_chain ht hu hε (h _ (boxMesh_pos hε))

/-- An exact zero-or-one selector obstructs the native chain at the
prescribed inverse-polynomial scale when the selector endpoints differ. -/
theorem no_native_chain_of_selector {t u : J → ℚ} (ht : Solution P t) (hu : Solution P u)
    (j : J) (h0 : t j = 0) (h1 : u j = 1)
    (hg : ∀ q, Solution P q → q j = 0 ∨ q j = 1) :
    ¬ (instrument (catalogue P) B).Chain (nativeMesh J T X 1) (lift B t ht) (lift B u hu) := by
  intro h
  have hc : BoxChain (P := P) 1 t u := by
    simpa only [decode_lift] using decode_chain rfl rfl zero_lt_one h
  have hzero (q : J → ℚ) (hpath : BoxChain (P := P) 1 t q) : q j = 0 := by
    induction hpath with
    | refl => exact h0
    | @tail a b hab hedge ih =>
      rcases hg b hedge.2.1 with hb | hb
      · exact hb
      · have hh := hedge.2.2 j
        rw [ih, hb] at hh
        norm_num at hh
  have he := hzero u hc
  rw [h1] at he
  norm_num at he

/-- Two upper bounds express one affine equality by complementing
the nonnegative terms. -/
theorem affine_rows {u v b total : ℚ} (h : u + v = total) :
    (u ≤ b ∧ v ≤ total - b) ↔ u = b := by
  constructor
  · rintro ⟨hu,hv⟩
    linarith
  · intro hu
    exact ⟨hu.le, by linarith⟩

theorem copy_rows {u v : ℚ} : (u + (1-v) ≤ 1 ∧ v + (1-u) ≤ 1) ↔ u = v := by
  constructor
  · rintro ⟨h,h'⟩
    linarith
  · intro h
    constructor <;> linarith

theorem square_rows {t z : ℚ} :
    (t^2 + (1-z) ≤ 1 ∧ (1-t) + t*(1-t) + z ≤ 1) ↔ z = t^2 := by
  constructor
  · rintro ⟨h,h'⟩
    nlinarith
  · intro h
    rw [h]
    constructor <;> nlinarith

theorem multiply_by_squares (u v z : ℚ) :
    (2*z = 4*((u+v)/2)^2 - u^2 - v^2) ↔ z = u*v := by
  constructor <;> intro h <;> nlinarith

end MovingProjection.ResponseBudgets
