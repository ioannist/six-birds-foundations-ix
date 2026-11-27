import MovingProjection.BooleanEvents
import MovingProjection.RationalBridge

/-! The rational-solvability reduction for local arithmetic circuit equations.
All gate constraints are expressed directly in the same native event language
as the Boolean reduction. The two supplied endpoints are always lawful. -/

namespace MovingProjection.OneStateEvents.ArithmeticReduction

open scoped BigOperators
open SignedExpr

variable {I : Type}

inductive Gate (I : Type) where
  | zero (z : I)
  | one (z : I)
  | add (z a b : I)
  | neg (z a : I)
  | mul (z a b : I)

def Gate.holds (v : I → ℚ) : Gate I → Prop
  | .zero z => v z = 0
  | .one z => v z = 1
  | .add z a b => v z = v a + v b
  | .neg z a => v z = -v a
  | .mul z a b => v z = v a * v b

def Solvable (gates : List (Gate I)) : Prop := ∃ v : I → ℚ, ∀ g ∈ gates, g.holds v

abbrev Coordinates (I : Type) := I ⊕ Fin 4

private def selector : Coordinates I := .inr 0
private def denominator : Coordinates I := .inr 1
private def radical : Coordinates I := .inr 2
private def slack : Coordinates I := .inr 3

private def p (i : I) : Pair (Coordinates I) := sub (coord (.inl i)) one
private def q : Pair (Coordinates I) := coord denominator
private def w : Pair (Coordinates I) := add one (coord radical)
private def u : Pair (Coordinates I) := sub (coord slack) one
private def s : Pair (Coordinates I) := coord selector
private def two : Pair (Coordinates I) := add one one

private def gated (t : Pair (Coordinates I)) : Pair (Coordinates I) :=
  mul (mul s (sub two s)) t

private def Gate.residual : Gate I → Pair (Coordinates I)
  | .zero z => p z
  | .one z => sub (p z) q
  | .add z a b => sub (p z) (SignedExpr.add (p a) (p b))
  | .neg z a => SignedExpr.add (p z) (p a)
  | .mul z a b => sub (SignedExpr.mul q (p z)) (SignedExpr.mul (p a) (p b))

private def slackResidual : Pair (Coordinates I) := sub (mul w w) (add two (mul (mul q q) u))

def compile (gates : List (Gate I)) : Equations (Coordinates I) :=
  gated slackResidual :: gates.map (fun g => gated g.residual)

private theorem holds_iff (gates : List (Gate I)) (x : Coordinates I → ℚ) :
    (compile gates).holds x ↔
      (eval s x * (2 - eval s x) * eval slackResidual x = 0) ∧
        (∀ g ∈ gates, eval s x * (2 - eval s x) * eval g.residual x = 0) := by
  have h (t : Pair (Coordinates I)) :
      (gated t).1.eval x = (gated t).2.eval x ↔
        eval s x * (2 - eval s x) * eval t x = 0 := by
    rw [← sub_eq_zero]
    change eval (gated t) x = 0 ↔ _
    norm_num [gated, two]
  constructor
  · intro hh
    exact ⟨(h _).mp (hh _ (List.mem_cons_self ..)), fun g hg =>
      (h _).mp (hh _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hg)))⟩
  · rintro ⟨hs, hg⟩ t ht
    simp only [compile, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨g, hmem, rfl⟩
    · exact (h _).mpr hs
    · exact (h _).mpr (hg g hmem)

private theorem residual_iff (g : Gate I) (x : Coordinates I → ℚ) (hq : eval q x ≠ 0) :
    eval g.residual x = 0 ↔ g.holds (fun i => eval (p i) x / eval q x) := by
  cases g <;> simp only [Gate.residual, Gate.holds, eval_sub, eval_add, eval_mul]
  · rw [div_eq_zero_iff]
    simp [hq]
  · rw [div_eq_iff hq]
    ring_nf
    exact sub_eq_zero
  · rw [← add_div, div_left_inj' hq]
    exact sub_eq_zero
  · rw [← neg_div, div_left_inj' hq]
    exact add_eq_zero_iff_eq_neg
  · rw [div_mul_div_comm, div_eq_div_iff hq (mul_ne_zero hq hq)]
    constructor
    · intro h
      linear_combination (eval q x) * h
    · intro h
      apply mul_left_cancel₀ hq
      linear_combination h

private theorem slack_eval (x : Coordinates I → ℚ) :
    eval slackResidual x = (eval w x)^2 - (2 + (eval q x)^2 * eval u x) := by
  simp only [slackResidual, eval_sub, eval_mul, eval_add]
  rw [show eval (two : Pair (Coordinates I)) x = 2 by norm_num [two]]
  ring

theorem interior_solves {gates : List (Gate I)} {x : Coordinates I → ℚ}
    (hx : (compile gates).BoxLawful x) (hs : x selector ≠ 0) (hs' : x selector ≠ 1) :
    Solvable gates := by
  have hscale : eval s x * (2 - eval s x) ≠ 0 := by
    simp only [s, eval_coord, mul_ne_zero_iff]
    constructor
    · exact ⟨by norm_num, hs⟩
    · intro h
      apply hs'
      linarith
  have h := (holds_iff gates x).mp hx.2
  have hslack := (mul_eq_zero.mp h.1).resolve_left hscale
  have hq : eval q x ≠ 0 := by
    intro hz
    have hw : 0 ≤ eval w x := by
      simp only [w, eval_add, eval_one, eval_coord]
      linarith [(hx.1 radical).1]
    rw [slack_eval, hz] at hslack
    apply RationalBridge.no_rational_sqrt_two _ hw
    nlinarith
  exact ⟨_, fun g hg =>
    (residual_iff g x hq).mp ((mul_eq_zero.mp (h.2 g hg)).resolve_left hscale)⟩

private def base (t : ℚ) : Coordinates I → ℚ
  | .inl _ => 0
  | .inr j => if j = 0 then t else 0

private theorem base_selector (t : ℚ) : (base (I := I) t) selector = t := by
  simp [base, selector]

private theorem face_lawful {gates : List (Gate I)} {x : Coordinates I → ℚ} (hx : InBox x)
    (hs : x selector = 0 ∨ x selector = 1) : (compile gates).BoxLawful x := by
  refine ⟨hx, (holds_iff _ _).mpr ?_⟩
  have hh : eval s x * (2 - eval s x) = 0 := by
    rcases hs with h | h <;> norm_num [s, h]
  simp [hh]

private theorem base_lawful (gates : List (Gate I)) (b : Bool) :
    (compile gates).BoxLawful (base (ClauseReconfiguration.bit b)) := by
  apply face_lawful
  · rintro (i | j)
    · simp [base]
    · cases b <;> by_cases hj : j = 0 <;> simp [base, hj, ClauseReconfiguration.bit]
  · cases b <;> simp [base_selector, ClauseReconfiguration.bit]

private def line {J : Type} (a b : J → ℚ) (t : ℚ) : J → ℚ :=
  fun i => (1 - t) * a i + t * b i

private theorem line_in_box {J : Type} {a b : J → ℚ} (ha : InBox a) (hb : InBox b)
    {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : InBox (line a b t) := by
  intro i
  unfold line
  constructor
  · positivity [(ha i).1, (hb i).1, sub_nonneg.mpr h1]
  · have h := add_le_add (mul_le_mul_of_nonneg_left (ha i).2 (sub_nonneg.mpr h1))
      (mul_le_mul_of_nonneg_left (hb i).2 h0)
    linarith

private theorem line_fine {J : Type} (eqs : Equations J) {a b : J → ℚ}
    (ha : InBox a) (hb : InBox b)
    (hline : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → eqs.BoxLawful (line a b t)) :
    eqs.BoxFine a b := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn₀ : (0 : ℚ) < n := (div_pos one_pos hε).trans hn
  have hsmall : 1 / (n : ℚ) < ε := by
    apply (div_lt_iff₀ hn₀).mpr
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hn
  let sample (k : ℕ) := line a b ((k : ℚ) / n)
  have hlegal (k : ℕ) (hk : k ≤ n) : eqs.BoxLawful (sample k) :=
    hline _ (div_nonneg (Nat.cast_nonneg _) hn₀.le) ((div_le_one hn₀).mpr (by exact_mod_cast hk))
  have hmesh (k : ℕ) (hk : k ≤ n) : eqs.BoxChain ε (sample 0) (sample k) := by
    induction k with
    | zero => exact .refl
    | succ k ih =>
      have hk' := (Nat.le_succ k).trans hk
      refine (ih hk').tail ⟨hlegal k hk', hlegal (k + 1) hk, fun i => ?_⟩
      change |line a b ((k : ℚ) / n) i - line a b ((↑(k + 1) : ℚ) / n) i| < ε
      rw [show line a b ((k : ℚ) / n) i - line a b ((↑(k + 1) : ℚ) / n) i =
        (1 / (n : ℚ)) * (a i - b i) by simp only [line, Nat.cast_add, Nat.cast_one]; ring,
        abs_mul, abs_of_pos (div_pos one_pos hn₀)]
      apply lt_of_le_of_lt _ hsmall
      have hd : |a i - b i| ≤ 1 := abs_le.mpr ⟨by linarith [(ha i).1, (hb i).2],
        by linarith [(ha i).2, (hb i).1]⟩
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hd (div_nonneg zero_le_one hn₀.le)
  have h0 : sample 0 = a := by funext i; simp [sample, line]
  have h1 : sample n = b := by funext i; simp [sample, line, hn₀.ne']
  rw [← h0, ← h1]
  exact hmesh n le_rfl

variable [Fintype I]

private theorem witness_exists {gates : List (Gate I)} (h : Solvable gates) :
    ∃ a b : Coordinates I → ℚ, InBox a ∧ InBox b ∧ a selector = 0 ∧ b selector = 1 ∧
      ∀ t : ℚ, 0 ≤ t → t ≤ 1 → (compile gates).BoxLawful (line a b t) := by
  obtain ⟨v, hv⟩ := h
  let total : ℚ := ∑ i, |v i|
  have ht : 0 ≤ total := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let d : ℚ := 1 / (1 + total)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd₁ : d ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  obtain ⟨r, l, hr₁, hr₂, hl, hrl⟩ := RationalBridge.exists_bounded_slack hd hd₁
  let point (t : ℚ) (i : Coordinates I) : ℚ :=
    match i with
    | .inl j => (d * v j + 1) / 2
    | .inr j => if j = 0 then t else if j = 1 then d / 2 else if j = 2 then (r - 1) / 2 else (l + 1) / 2
  have hpoint (t : ℚ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : InBox (point t) := by
    rintro (i | j)
    · have hv' : |v i| ≤ total :=
        Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
      have hh : |d * v i| ≤ 1 := by
        rw [abs_mul, abs_of_pos hd]
        dsimp [d]
        rw [div_mul_eq_mul_div, one_mul]
        exact (div_le_one (by positivity)).mpr (by linarith)
      obtain ⟨hlo, hhi⟩ := abs_le.mp hh
      change 0 ≤ (d * v i + 1) / 2 ∧ (d * v i + 1) / 2 ≤ 1
      constructor <;> linarith
    · fin_cases j
      all_goals simp [point, ht₀, ht₁] <;>
        constructor <;> linarith [hd.le, hd₁, hr₁, hr₂, (abs_le.mp hl).1, (abs_le.mp hl).2]
  have hline (t : ℚ) : line (point 0) (point 1) t = point t := by
    funext i
    rcases i with i | j
    · simp only [line, point]; ring
    · by_cases hj : j = 0 <;> simp only [line, point, hj, if_true, if_false] <;> ring
  have hp (t : ℚ) (i : I) : eval (p i) (point t) = d * v i := by
    simp [p, point]; ring
  have hq (t : ℚ) : eval q (point t) = d := by
    change 1 + 2 * (d / 2) - 1 = d
    ring
  have hw (t : ℚ) : eval w (point t) = r := by
    simp only [w, eval_add, eval_one, eval_coord]
    change 1 + 2 * ((r - 1) / 2) = r
    ring
  have hu (t : ℚ) : eval u (point t) = l := by
    simp only [u, eval_sub, eval_one, eval_coord]
    change 2 * ((l + 1) / 2) - 1 = l
    ring
  refine ⟨point 0, point 1, hpoint _ (by norm_num) (by norm_num),
    hpoint _ (by norm_num) (by norm_num), rfl, rfl, fun t ht₀ ht₁ => ?_⟩
  rw [hline]
  refine ⟨hpoint _ ht₀ ht₁, (holds_iff _ _).mpr ⟨?_, ?_⟩⟩
  · rw [slack_eval, hw, hq, hu, hrl, sub_self, mul_zero]
  · intro g hg
    have hzero := (residual_iff g (point t) (by rw [hq]; exact hd.ne')).mpr
      (show g.holds (fun i => eval (p i) (point t) / eval q (point t)) from by
        have he : (fun i => eval (p i) (point t) / eval q (point t)) = v := by
          funext i
          rw [hp, hq, mul_comm, mul_div_cancel_right₀ _ hd.ne']
        rw [he]
        exact hv g hg)
    rw [hzero, mul_zero]

private theorem cube_yes {gates : List (Gate I)} (h : Solvable gates) :
    (compile gates).BoxFine (base 0) (base 1) := by
  obtain ⟨a, b, ha, hb, hsa, hsb, hab⟩ := witness_exists h
  have hf (c d : Coordinates I → ℚ) (hc : InBox c) (hd : InBox d)
      (he : c selector = d selector) (hz : c selector = 0 ∨ c selector = 1) :
      (compile gates).BoxFine c d := by
    apply line_fine _ hc hd
    intro t ht₀ ht₁
    apply face_lawful (line_in_box hc hd ht₀ ht₁)
    simpa only [show line c d t selector = c selector by simp only [line, ← he]; ring] using hz
  have hx := (base_lawful gates false).1
  have hy := (base_lawful gates true).1
  change InBox (base 0) at hx
  change InBox (base 1) at hy
  have hfirst := hf (base 0) a hx ha (by rw [base_selector, hsa]) (Or.inl (base_selector 0))
  have hlast := hf b (base 1) hb hy (by rw [base_selector, hsb]) (Or.inr hsb)
  intro ε hε
  exact ((hfirst ε hε).trans (line_fine _ ha hb hab ε hε)).trans (hlast ε hε)

omit [Fintype I] in
private theorem cube_no {gates : List (Gate I)} (h : ¬ Solvable gates) :
    ¬ (compile gates).BoxChain 1 (base 0) (base 1) := by
  have hside (x : Coordinates I → ℚ) (hx : (compile gates).BoxLawful x) :
      x selector = 0 ∨ x selector = 1 := by
    by_contra! hh
    exact h (interior_solves hx hh.1 hh.2)
  intro hc
  have hz : ∀ y, (compile gates).BoxChain 1 (base 0) y → y selector = 0 := by
    intro y hh
    induction hh with
    | refl => exact base_selector 0
    | tail _ e ih =>
      rcases hside _ e.2.1 with h0 | h1
      · exact h0
      · have he := e.2.2 selector
        rw [ih, h1] at he
        norm_num at he
  have he := hz (base 1) hc
  norm_num [base_selector] at he

variable [DecidableEq I]

noncomputable def endpoint (gates : List (Gate I)) (b : Bool) :=
  (compile gates).nativePoint (base (ClauseReconfiguration.bit b)) (base_lawful gates b)

theorem endpoints_distinct (gates : List (Gate I)) : endpoint gates false ≠ endpoint gates true := by
  intro he
  have hr := congrArg (fun u => (compile gates).decode u.val.law.rate selector) he
  change (compile gates).decode ((compile gates).encode (base 0)) selector =
    (compile gates).decode ((compile gates).encode (base 1)) selector at hr
  norm_num [Equations.decode_encode, base_selector] at hr

theorem native_chain_iff_solvable (gates : List (Gate I)) :
    (compile gates).NativeChain (2 * (compile gates).floor)
      (endpoint gates false) (endpoint gates true) ↔ Solvable gates := by
  rw [endpoint, endpoint, Equations.nativePoint_chain_iff]
  change Chain (compile gates).tests (compile gates).floor (2 * (compile gates).floor)
    ((compile gates).encode (base 0)) ((compile gates).encode (base 1)) ↔ _
  constructor
  · intro h
    by_contra hn
    apply cube_no hn
    have hc : Chain (compile gates).tests (compile gates).floor (2 * (compile gates).floor * 1)
        ((compile gates).encode (base 0)) ((compile gates).encode (base 1)) := by simpa using h
    simpa using (compile gates).decode_chain hc
  · intro h
    exact ((compile gates).fine_encode_iff _ _).mpr (cube_yes h) _
      (mul_pos (by norm_num) (compile gates).floor_pos)

theorem native_fine_iff_solvable (gates : List (Gate I)) :
    (∀ ε : ℚ, 0 < ε → (compile gates).NativeChain ε
      (endpoint gates false) (endpoint gates true)) ↔ Solvable gates := by
  constructor
  · intro h
    exact (native_chain_iff_solvable gates).mp
      (h (2 * (compile gates).floor) (mul_pos (by norm_num) (compile gates).floor_pos))
  · intro h ε hε
    rw [endpoint, endpoint, Equations.nativePoint_chain_iff]
    exact ((compile gates).fine_encode_iff _ _).mpr (cube_yes h) ε hε

theorem native_chain_iff_solvable_of_le (gates : List (Gate I))
    {ε : ℚ} (hε : 0 < ε) (hle : ε ≤ 2 * (compile gates).floor) :
    (compile gates).NativeChain ε (endpoint gates false) (endpoint gates true) ↔ Solvable gates := by
  constructor
  · intro h
    exact (native_chain_iff_solvable gates).mp ((compile gates).nativeChain_mono h hle)
  · intro h
    exact (native_fine_iff_solvable gates).mpr h ε hε

end MovingProjection.OneStateEvents.ArithmeticReduction
