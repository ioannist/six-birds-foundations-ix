import MovingProjection.Spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! Protected word equations in the logarithmic coordinates of a sign chart. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I]

def realMonomial (e : I → ℕ) (x : I → ℝ) : ℝ :=
  ∏ i, x i ^ e i

noncomputable def realSupport (x : I → ℝ) : Finset I :=
  Finset.univ.filter fun i => x i ≠ 0

@[simp] theorem mem_realSupport {x : I → ℝ} {i : I} :
    i ∈ realSupport x ↔ x i ≠ 0 := by
  simp [realSupport]

theorem realMonomial_cast (e : I → ℕ) (x : I → ℚ) :
    realMonomial e (fun i => (x i : ℝ)) = (monomial e x : ℝ) := by
  simp [realMonomial, monomial]

theorem realSupport_cast (x : I → ℚ) :
    realSupport (fun i => (x i : ℝ)) = support x := by
  ext i
  simp

theorem real_log_monomial (e : I → ℕ) (x : I → ℝ)
    (h : ∀ i, x i = 0 → e i = 0) :
    Real.log (realMonomial e x) = ∑ i, (e i : ℝ) * Real.log (x i) := by
  unfold realMonomial
  rw [Real.log_prod]
  · simp only [Real.log_pow]
  · intro i _
    by_cases hz : x i = 0
    · simp [h i hz]
    · exact pow_ne_zero _ hz

theorem log_equation (r : MonomialTest I) (x : I → ℝ)
    (ha : r.row.active (realSupport x))
    (h : realMonomial r.row.lhs x = (r.ratio : ℝ) * realMonomial r.row.rhs x) :
    (∑ i, ((r.row.lhs i : ℝ) - (r.row.rhs i : ℝ)) * Real.log (x i)) =
      Real.log (r.ratio : ℝ) := by
  have hzero (i : I) (hi : x i = 0) : r.row.lhs i = 0 ∧ r.row.rhs i = 0 :=
    ha i (by simp [hi])
  have hl : realMonomial r.row.lhs x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases hz : x i = 0
    · simp [(hzero i hz).1]
    · exact pow_ne_zero _ hz
  have hr : (r.ratio : ℝ) ≠ 0 ∧ realMonomial r.row.rhs x ≠ 0 := by
    exact mul_ne_zero_iff.mp (h ▸ hl)
  have logh := congrArg Real.log h
  rw [Real.log_mul hr.1 hr.2, real_log_monomial _ _ (fun i hi => (hzero i hi).1),
    real_log_monomial _ _ (fun i hi => (hzero i hi).2)] at logh
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith

end MovingProjection
