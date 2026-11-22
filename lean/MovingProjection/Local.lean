import MovingProjection.Spectral
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Discretization of a legal damping curve into arbitrarily small rational steps. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I]

def LocalStep (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (ε : ℚ) (x y : I → ℚ) : Prop :=
  Legal tests budgets x ∧ Legal tests budgets y ∧ ∀ i, |x i - y i| < ε

def FineConnected (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (x y : I → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (LocalStep tests budgets ε) x y

theorem FineConnected.refl (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (x : I → ℚ) : FineConnected tests budgets x x := fun _ _ => .refl

theorem FineConnected.trans {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y z : I → ℚ} (hxy : FineConnected tests budgets x y)
    (hyz : FineConnected tests budgets y z) : FineConnected tests budgets x z :=
  fun ε hε => (hxy ε hε).trans (hyz ε hε)

theorem FineConnected.symm {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y : I → ℚ} (hxy : FineConnected tests budgets x y) : FineConnected tests budgets y x := by
  intro ε hε
  have h := hxy ε hε
  clear hxy
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    have hreverse : LocalStep tests budgets ε _ _ :=
      ⟨hstep.2.1, hstep.1, fun i => by simpa only [abs_sub_comm] using hstep.2.2 i⟩
    exact .head hreverse ih

private theorem power_difference (t u : ℚ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (n : ℕ) :
    |t^n - u^n| ≤ (n : ℚ) * |t-u| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : t^(n+1) - u^(n+1) = t^n*(t-u) + (t^n-u^n)*u := by
      simp only [pow_succ]
      ring
    rw [heq]
    calc
      _ ≤ |t^n*(t-u)| + |(t^n-u^n)*u| := abs_add_le _ _
      _ ≤ |t-u| + (n : ℚ)*|t-u| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht₀ n), abs_of_nonneg hu₀]
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ ht₀ ht₁ (n := n))
            (abs_nonneg (t-u))
        · exact (mul_le_mul_of_nonneg_left hu₁ (abs_nonneg (t^n-u^n))).trans (by simpa using ih)
      _ = _ := by push_cast; ring

theorem fineConnected_scale {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℚ} (hx : Legal tests budgets x) {w : I → ℕ}
    (hw : Damping (tests.map MonomialTest.row) (support x) w) :
    FineConnected tests budgets (scale x w 0) x := by
  intro ε hε
  let B : ℚ := 1 + ∑ i, |x i| * (w i : ℚ)
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ε)
  let N : ℕ := n + 1
  have hN : 0 < (N : ℚ) := by exact_mod_cast Nat.succ_pos n
  have hB : B < (N : ℚ) * ε := by
    have ht : B < (n : ℚ) * ε := (div_lt_iff₀ hε).1 hn
    have hnN : (n : ℚ) ≤ (N : ℚ) := by exact_mod_cast Nat.le_succ n
    exact ht.trans_le (mul_le_mul_of_nonneg_right hnN hε.le)
  have hsmall : B / (N : ℚ) < ε := (div_lt_iff₀ hN).2 (by simpa [mul_comm] using hB)
  let t (k : ℕ) : ℚ := (k : ℚ) / (N : ℚ)
  have hparam (k : ℕ) (hk : k ≤ N) : 0 ≤ t k ∧ t k ≤ 1 := by
    refine ⟨div_nonneg (by positivity) hN.le, (div_le_iff₀ hN).2 ?_⟩
    simpa using (show (k : ℚ) ≤ (N : ℚ) by exact_mod_cast hk)
  have hstep (k : ℕ) (hk : k+1 ≤ N) :
      LocalStep tests budgets ε (scale x w (t k)) (scale x w (t (k+1))) := by
    have hp := hparam k ((Nat.le_succ k).trans hk)
    have hq := hparam (k+1) hk
    refine ⟨hx.scale hw hp.1 hp.2, hx.scale hw hq.1 hq.2, fun i => ?_⟩
    have hdist : |t k - t (k+1)| = 1 / (N : ℚ) := by
      have hd : t k - t (k+1) = -(1/(N : ℚ)) := by
        simp only [t, Nat.cast_add, Nat.cast_one]
        ring
      rw [hd, abs_neg, abs_of_nonneg (by positivity)]
    have hb : |x i| * (w i : ℚ) ≤ B := by
      have hle : |x i| * (w i : ℚ) ≤ ∑ j, |x j| * (w j : ℚ) :=
        Finset.single_le_sum (f := fun j => |x j| * (w j : ℚ))
          (fun _ _ => by positivity) (Finset.mem_univ i)
      exact hle.trans (by dsimp [B]; linarith)
    calc
      _ = |x i| * |(t k)^(w i)-(t (k+1))^(w i)| := by
        simp only [scale, ← mul_sub, abs_mul]
      _ ≤ |x i| * ((w i : ℚ) * |t k-t (k+1)|) :=
        mul_le_mul_of_nonneg_left (power_difference _ _ hp.1 hp.2 hq.1 hq.2 _) (abs_nonneg _)
      _ ≤ B / (N : ℚ) := by
        rw [hdist, ← mul_assoc, mul_one_div]
        exact div_le_div_of_nonneg_right hb hN.le
      _ < ε := hsmall
  have hchain (k : ℕ) (hk : k ≤ N) :
      Relation.ReflTransGen (LocalStep tests budgets ε) (scale x w (t 0)) (scale x w (t k)) := by
    induction k with
    | zero => exact .refl
    | succ k ih => exact (ih ((Nat.le_succ k).trans hk)).tail (hstep k hk)
  have hstart : scale x w (t 0) = scale x w 0 := by simp [t]
  have hfinish : scale x w (t N) = x := by
    have heq : t N = 1 := div_self hN.ne'
    funext i
    simp [heq, scale]
  simpa only [hstart, hfinish] using hchain N (Nat.le_refl N)

theorem fineConnected_to_core [DecidableEq I]
    {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℚ} (hx : Legal tests budgets x) :
    ∃ y, Legal tests budgets y ∧ FineConnected tests budgets x y ∧
      support y = core (tests.map MonomialTest.row) (support x) ∧
      ∀ i ∈ support y, y i = x i := by
  suffices h : ∀ s, Reduces (tests.map MonomialTest.row) (support x) s →
      ∃ y, Legal tests budgets y ∧ FineConnected tests budgets x y ∧
        support y = s ∧ ∀ i ∈ support y, y i = x i by
    exact h _ (isCore_core _ _).1
  intro s hs
  induction hs with
  | refl => exact ⟨x, hx, FineConnected.refl _ _ _, rfl, fun _ _ => rfl⟩
  | @tail u v _ hstep ih =>
    obtain ⟨y, hy, hxy, hyu, hval⟩ := ih
    rw [← hyu] at hstep
    obtain ⟨w, hw, hv⟩ := hstep
    refine ⟨scale y w 0, hy.scale hw le_rfl (by norm_num), ?_, ?_, ?_⟩
    · exact hxy.trans (fineConnected_scale hy hw).symm
    · exact (support_scale_zero y w).trans hv.symm
    · intro i hi
      rw [support_scale_zero] at hi
      obtain ⟨hy', hw'⟩ := Finset.mem_filter.mp hi
      simp [scale, hw', hval i hy']

end MovingProjection
