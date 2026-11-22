import MovingProjection.Contraction
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-! Rational realization of every permitted spectral contraction. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I]

structure MonomialTest (I : Type*) where
  row : ExponentRow I
  ratio : ℚ

structure MarkBudget (I : Type*) where
  indices : Finset I
  cap : ℚ

def monomial (f : I → ℕ) (x : I → ℚ) : ℚ :=
  ∏ i, x i ^ f i

def MonomialTest.holds (r : MonomialTest I) (x : I → ℚ) : Prop :=
  monomial r.row.lhs x = r.ratio * monomial r.row.rhs x

def Legal (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (x : I → ℚ) : Prop :=
  (∀ r ∈ tests, r.holds x) ∧
    ∀ b ∈ budgets, ∑ i ∈ b.indices, |x i| ≤ b.cap

def support (x : I → ℚ) : Finset I :=
  Finset.univ.filter fun i => x i ≠ 0

@[simp] theorem mem_support {x : I → ℚ} {i : I} : i ∈ support x ↔ x i ≠ 0 := by
  simp [support]

def scale (x : I → ℚ) (w : I → ℕ) (t : ℚ) : I → ℚ :=
  fun i => x i * t ^ w i

theorem monomial_scale (f : I → ℕ) (x : I → ℚ) (w : I → ℕ) (t : ℚ) :
    monomial f (scale x w t) = monomial f x * t ^ (∑ i, f i * w i) := by
  calc
    _ = ∏ i, (x i ^ f i) * t ^ (f i * w i) := by
      unfold monomial
      apply Finset.prod_congr rfl
      intro i _
      rw [scale, mul_pow, ← pow_mul, Nat.mul_comm (w i)]
    _ = _ := by rw [monomial, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem monomial_eq_zero_of_factor (f : I → ℕ) {x : I → ℚ} {i : I}
    (hx : x i = 0) (hf : f i ≠ 0) : monomial f x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hx, zero_pow hf]

theorem MonomialTest.holds_scale {r : MonomialTest I} {x : I → ℚ}
    (h : r.holds x) (w : I → ℕ) (t : ℚ)
    (hweight : r.row.active (support x) →
        ∑ i, r.row.lhs i * w i = ∑ i, r.row.rhs i * w i) :
    r.holds (scale x w t) := by
  unfold MonomialTest.holds at *
  rw [monomial_scale, monomial_scale]
  by_cases ha : r.row.active (support x)
  · rw [hweight ha, h, mul_assoc]
  · classical
    have hzWitness : ∃ i, x i = 0 ∧ (r.row.lhs i ≠ 0 ∨ r.row.rhs i ≠ 0) := by
      by_contra hn
      apply ha
      intro i hi
      have hz : x i = 0 := by simpa using hi
      constructor
      · by_contra hne
        exact hn ⟨i, hz, Or.inl hne⟩
      · by_contra hne
        exact hn ⟨i, hz, Or.inr hne⟩
    obtain ⟨i, hi, hleft | hright⟩ := hzWitness
    · have hz := monomial_eq_zero_of_factor r.row.lhs hi hleft
      have hc : r.ratio * monomial r.row.rhs x = 0 := h.symm.trans hz
      rw [← mul_assoc, hz, hc]
      simp
    · have hz := monomial_eq_zero_of_factor r.row.rhs hi hright
      rw [hz] at h ⊢
      simp [h]

theorem Legal.scale {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℚ} (hx : Legal tests budgets x) {w : I → ℕ}
    (hw : Damping (tests.map MonomialTest.row) (support x) w)
    {t : ℚ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : Legal tests budgets (scale x w t) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    exact MonomialTest.holds_scale (hx.1 c hc) w t
      (hw.2 c.row (List.mem_map_of_mem hc))
  · intro b hb
    apply le_trans _ (hx.2 b hb)
    apply Finset.sum_le_sum
    intro i _
    rw [MovingProjection.scale, abs_mul, abs_of_nonneg (pow_nonneg ht₀ _)]
    simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ ht₀ ht₁ (n := w i))
      (abs_nonneg (x i))

theorem support_scale_zero (x : I → ℚ) (w : I → ℕ) :
    support (scale x w 0) = (support x).filter (fun i => w i = 0) := by
  ext i
  by_cases hw : w i = 0
  · simp [scale, hw]
  · simp [scale, hw, zero_pow hw]

theorem rational_contraction {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℚ} (hx : Legal tests budgets x) {s : Finset I}
    (hs : Contracts (tests.map MonomialTest.row) (support x) s) :
    ∃ w : I → ℕ,
      (∀ t : ℚ, 0 ≤ t → t ≤ 1 → Legal tests budgets (scale x w t)) ∧
      scale x w 1 = x ∧ support (scale x w 0) = s := by
  obtain ⟨w, hw, rfl⟩ := hs
  refine ⟨w, fun _ ht₀ ht₁ => hx.scale hw ht₀ ht₁, ?_, support_scale_zero x w⟩
  funext i
  simp [scale]

end MovingProjection
