import MovingProjection.OneStateEvents
import Mathlib.Data.Nat.Log

/-! Positive expressions in the two rates of each box coordinate. A node
has a value bound and a variation bound on the unit cube. These bounds
allow the compiler to use a common reference rate and fixed-sum pairs. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

inductive Expr (I : Type) where
  | one
  | coordinate (i : I) (complement : Bool)
  | add (left right : Expr I)
  | mul (left right : Expr I)
  deriving DecidableEq

variable {I : Type}

def InBox (x : I → ℚ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

def unitRate (x : I → ℚ) (i : I) (complement : Bool) : ℚ :=
  if complement then 3 - 2 * x i else 1 + 2 * x i

theorem unitRate_pair (x : I → ℚ) (i : I) : unitRate x i false + unitRate x i true = 4 := by
  norm_num [unitRate]

theorem unitRate_bounds {x : I → ℚ} (hx : InBox x) (i : I) (complement : Bool) :
    1 ≤ unitRate x i complement ∧ unitRate x i complement ≤ 3 := by
  have h := hx i
  cases complement <;> simp only [unitRate, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> linarith

theorem unitRate_sub (x y : I → ℚ) (i : I) (complement : Bool) :
    |unitRate x i complement - unitRate y i complement| = 2 * |x i - y i| := by
  cases complement
  · rw [show unitRate x i false - unitRate y i false = 2 * (x i - y i) by simp [unitRate]; ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  · rw [show unitRate x i true - unitRate y i true = 2 * (y i - x i) by simp [unitRate]; ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2), abs_sub_comm (y i) (x i)]

namespace Expr

def eval (x : I → ℚ) : Expr I → ℚ
  | .one => 1
  | .coordinate i b => unitRate x i b
  | .add a b => eval x a + eval x b
  | .mul a b => eval x a * eval x b

def bound : Expr I → ℕ
  | .one => 1
  | .coordinate _ _ => 3
  | .add a b => bound a + bound b
  | .mul a b => bound a * bound b

def slope : Expr I → ℕ
  | .one => 0
  | .coordinate _ _ => 2
  | .add a b => slope a + slope b
  | .mul a b => bound a * slope b + bound b * slope a

theorem eval_bounds {x : I → ℚ} (hx : InBox x) (e : Expr I) :
    1 ≤ e.eval x ∧ e.eval x ≤ e.bound := by
  induction e with
  | one => norm_num [eval, bound]
  | coordinate i b => simpa [eval, bound] using unitRate_bounds hx i b
  | add a b ha hb =>
    constructor
    · simp only [eval]; linarith [ha.1, hb.1]
    · simp only [eval, bound, Nat.cast_add]; exact add_le_add ha.2 hb.2
  | mul a b ha hb =>
    constructor
    · simp only [eval]
      exact one_le_mul_of_one_le_of_one_le ha.1 hb.1
    · simp only [eval, bound, Nat.cast_mul]
      exact mul_le_mul ha.2 hb.2 (zero_le_one.trans hb.1) (by positivity)

theorem eval_variation {x y : I → ℚ} (hx : InBox x) (hy : InBox y) {t : ℚ}
    (hclose : ∀ i, |x i - y i| ≤ t) (e : Expr I) :
    |e.eval x - e.eval y| ≤ e.slope * t := by
  induction e with
  | one => simp [eval, slope]
  | coordinate i b =>
    simp only [eval, slope, Nat.cast_ofNat, unitRate_sub]
    exact mul_le_mul_of_nonneg_left (hclose i) (by norm_num)
  | add a b ha hb =>
    simp only [eval, slope, Nat.cast_add, add_mul]
    rw [show a.eval x + b.eval x - (a.eval y + b.eval y) =
      (a.eval x - a.eval y) + (b.eval x - b.eval y) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha hb)
  | mul a b ha hb =>
    have hax := eval_bounds hx a
    have hby := eval_bounds hy b
    simp only [eval, slope, Nat.cast_add, Nat.cast_mul, add_mul, mul_assoc]
    rw [show a.eval x * b.eval x - a.eval y * b.eval y =
      a.eval x * (b.eval x - b.eval y) + b.eval y * (a.eval x - a.eval y) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (zero_le_one.trans hax.1)]
      exact mul_le_mul hax.2 hb (abs_nonneg _) (by positivity)
    · rw [abs_mul, abs_of_nonneg (zero_le_one.trans hby.1)]
      exact mul_le_mul hby.2 ha (abs_nonneg _) (by positivity)

def subexpressions : Expr I → List (Expr I)
  | .one => [.one]
  | .coordinate i b => [.coordinate i b]
  | .add a b => .add a b :: (subexpressions a ++ subexpressions b)
  | .mul a b => .mul a b :: (subexpressions a ++ subexpressions b)

theorem self_mem_subexpressions (e : Expr I) : e ∈ e.subexpressions := by
  cases e <;> simp [subexpressions]

theorem subexpressions_trans {e f g : Expr I}
    (hf : f ∈ e.subexpressions) (hg : g ∈ f.subexpressions) : g ∈ e.subexpressions := by
  induction e with
  | one => simp [subexpressions] at hf; simpa [hf] using hg
  | coordinate i b => simp [subexpressions] at hf; simpa [hf] using hg
  | add a b ha hb =>
    simp only [subexpressions, List.mem_cons, List.mem_append] at hf ⊢
    rcases hf with rfl | ha' | hb'
    · simpa [subexpressions] using hg
    · exact Or.inr (Or.inl (ha ha'))
    · exact Or.inr (Or.inr (hb hb'))
  | mul a b ha hb =>
    simp only [subexpressions, List.mem_cons, List.mem_append] at hf ⊢
    rcases hf with rfl | ha' | hb'
    · simpa [subexpressions] using hg
    · exact Or.inr (Or.inl (ha ha'))
    · exact Or.inr (Or.inr (hb hb'))

end Expr

abbrev Equations (I : Type) := List (Expr I × Expr I)

def Equations.holds (eqs : Equations I) (x : I → ℚ) : Prop :=
  ∀ eq ∈ eqs, eq.1.eval x = eq.2.eval x

def Equations.nodes [DecidableEq I] (eqs : Equations I) : Finset (Expr I) :=
  (eqs.flatMap fun eq => eq.1.subexpressions ++ eq.2.subexpressions).toFinset

theorem Equations.subexpression_mem [DecidableEq I] {eqs : Equations I} {e f : Expr I}
    (he : e ∈ eqs.nodes) (hf : f ∈ e.subexpressions) : f ∈ eqs.nodes := by
  simp only [nodes, List.mem_toFinset, List.mem_flatMap, List.mem_append] at he ⊢
  obtain ⟨eq, h, hl | hr⟩ := he
  · exact ⟨eq, h, Or.inl (Expr.subexpressions_trans hl hf)⟩
  · exact ⟨eq, h, Or.inr (Expr.subexpressions_trans hr hf)⟩

theorem Equations.left_mem [DecidableEq I] {eqs : Equations I} {eq : Expr I × Expr I}
    (he : eq ∈ eqs) : eq.1 ∈ eqs.nodes := by
  simp only [nodes, List.mem_toFinset, List.mem_flatMap, List.mem_append]
  exact ⟨eq, he, Or.inl (eq.1.self_mem_subexpressions)⟩

theorem Equations.right_mem [DecidableEq I] {eqs : Equations I} {eq : Expr I × Expr I}
    (he : eq ∈ eqs) : eq.2 ∈ eqs.nodes := by
  simp only [nodes, List.mem_toFinset, List.mem_flatMap, List.mem_append]
  exact ⟨eq, he, Or.inr (eq.2.self_mem_subexpressions)⟩

end MovingProjection.OneStateEvents
