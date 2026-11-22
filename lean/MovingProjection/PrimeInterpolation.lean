import MovingProjection.LogEquations
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Integer prime exponents give exact rational parameters for the logarithmic segment. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I]

def primesOf (q : ℚ) : Finset ℕ :=
  q.num.natAbs.primeFactors ∪ q.den.primeFactors

private theorem log_nat_on (n : ℕ) (p : Finset ℕ) (hp : n.primeFactors ⊆ p) :
    Real.log n = ∑ k ∈ p, (n.factorization k : ℝ) * Real.log k := by
  rw [Real.log_nat_eq_sum_factorization]
  exact Finset.sum_subset hp (fun k _ hk => by
    have hzero : n.factorization k = 0 := Finsupp.notMem_support_iff.mp hk
    simp [hzero])

theorem log_rat_on {q : ℚ} (hq : 0 < q) (p : Finset ℕ) (hp : primesOf q ⊆ p)
    (hprime : ∀ k ∈ p, Nat.Prime k) :
    Real.log (q : ℝ) = ∑ k ∈ p, (padicValRat k q : ℝ) * Real.log k := by
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have heq : (q : ℝ) = (q.num.natAbs : ℝ) / (q.den : ℝ) := by
    have h := congrArg (Rat.castHom ℝ) q.num_div_den
    change ((((q.num : ℚ) / q.den) : ℚ) : ℝ) = (q : ℝ) at h
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, ← hnum, Int.cast_natCast] at h
    exact h.symm
  have hn : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_pos.mpr hq).ne'
  rw [heq, Real.log_div (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr q.den_ne_zero)]
  rw [log_nat_on _ p (Finset.union_subset_iff.mp hp).1, log_nat_on _ p (Finset.union_subset_iff.mp hp).2]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorization_def _ (hprime k hk), Nat.factorization_def _ (hprime k hk)]
  simp only [padicValRat, padicValInt, Int.cast_sub, Int.cast_natCast]
  ring

theorem valuation_monomial {p : ℕ} [Fact p.Prime] (e : I → ℕ) (x : I → ℚ)
    (hx : ∀ i, x i ≠ 0) :
    padicValRat p (monomial e x) = ∑ i, (e i : ℤ) * padicValRat p (x i) := by
  classical
  unfold monomial
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      padicValRat.mul (pow_ne_zero _ (hx i))
        (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hx j)),
      padicValRat.pow (hx i), ih]

theorem valuation_balanced {p : ℕ} (hp : p.Prime) (r : MonomialTest I) (u : I → ℚ)
    (hu : ∀ i, u i ≠ 0) (h : monomial r.row.lhs u = monomial r.row.rhs u) :
    (∑ i, (r.row.lhs i : ℤ) * padicValRat p (u i)) =
      ∑ i, (r.row.rhs i : ℤ) * padicValRat p (u i) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← valuation_monomial _ _ hu, ← valuation_monomial _ _ hu, h]

theorem monomial_mul (e : I → ℕ) (x u : I → ℚ) :
    monomial e (fun i => x i * u i) = monomial e x * monomial e u := by
  simp only [monomial, mul_pow, Finset.prod_mul_distrib]

theorem monomial_ne_zero_of_active {r : MonomialTest I} {x : I → ℚ}
    (h : r.row.active (support x)) :
    monomial r.row.lhs x ≠ 0 ∧ monomial r.row.rhs x ≠ 0 := by
  have hzero (i : I) (hi : x i = 0) : r.row.lhs i = 0 ∧ r.row.rhs i = 0 := h i (by simp [hi])
  constructor <;> apply Finset.prod_ne_zero_iff.mpr <;> intro i _
  · by_cases hi : x i = 0
    · simp [(hzero i hi).1]
    · exact pow_ne_zero _ hi
  · by_cases hi : x i = 0
    · simp [(hzero i hi).2]
    · exact pow_ne_zero _ hi

def primeTransfer {P : Type*} [Fintype P] (z : I → P → ℤ) (v : P → ℚ) (i : I) : ℚ :=
  ∏ p, v p ^ z i p

noncomputable def realPrimeTransfer {P : Type*} [Fintype P]
    (z : I → P → ℤ) (v : P → ℝ) (i : I) : ℝ :=
  ∏ p, v p ^ z i p

omit [Fintype I] in
theorem realPrimeTransfer_cast {P : Type*} [Fintype P]
    (z : I → P → ℤ) (v : P → ℚ) (i : I) :
    realPrimeTransfer z (fun p => (v p : ℝ)) i = (primeTransfer z v i : ℝ) := by
  simp [realPrimeTransfer, primeTransfer]

omit [Fintype I] in
theorem realPrimeTransfer_log {P : Type*} [Fintype P]
    (z : I → P → ℤ) {v : P → ℝ} (hv : ∀ p, 0 < v p) (i : I) :
    Real.log (realPrimeTransfer z v i) = ∑ p, (z i p : ℝ) * Real.log (v p) := by
  unfold realPrimeTransfer
  rw [Real.log_prod (fun p _ => zpow_ne_zero _ (hv p).ne')]
  simp only [Real.log_zpow]

theorem primeTransfer_monomial {P : Type*} [Fintype P] (z : I → P → ℤ)
    {v : P → ℚ} (hv : ∀ p, 0 < v p) (r : ExponentRow I)
    (h : ∀ p, (∑ i, (r.lhs i : ℤ) * z i p) = ∑ i, (r.rhs i : ℤ) * z i p) :
    monomial r.lhs (primeTransfer z v) = monomial r.rhs (primeTransfer z v) := by
  have hvR (p : P) : 0 < (fun q => (v q : ℝ)) p := by
    change 0 < (v p : ℝ)
    exact_mod_cast hv p
  have hp (i : I) : 0 < (primeTransfer z v i : ℝ) := by
    rw [← realPrimeTransfer_cast]
    unfold realPrimeTransfer
    exact Finset.prod_pos fun p _ => zpow_pos (hvR p) _
  have hl : (0 : ℝ) < realMonomial r.lhs (fun i => (primeTransfer z v i : ℝ)) :=
    Finset.prod_pos fun i _ => pow_pos (hp i) _
  have hr : (0 : ℝ) < realMonomial r.rhs (fun i => (primeTransfer z v i : ℝ)) :=
    Finset.prod_pos fun i _ => pow_pos (hp i) _
  have he : realMonomial r.lhs (fun i => (primeTransfer z v i : ℝ)) =
      realMonomial r.rhs (fun i => (primeTransfer z v i : ℝ)) := by
    apply Real.log_injOn_pos hl hr
    rw [real_log_monomial _ _ (fun i hi => ((hp i).ne' hi).elim),
      real_log_monomial _ _ (fun i hi => ((hp i).ne' hi).elim)]
    simp only [← realPrimeTransfer_cast, realPrimeTransfer_log z hvR, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    have hf (e : I → ℕ) :
        (∑ i, (e i : ℝ) * ((z i p : ℝ) * Real.log (v p))) =
          (∑ i, (e i : ℝ) * (z i p : ℝ)) * Real.log (v p) := by
      simp only [mul_assoc, Finset.sum_mul]
    rw [hf, hf]
    congr 1
    exact_mod_cast h p
  rw [realMonomial_cast, realMonomial_cast] at he
  exact_mod_cast he

/-- A multiplicative change by positive factors preserving all active exponent
identities preserves the signed native equation. -/
theorem MonomialTest.holds_mul_positive (r : MonomialTest I) {x u : I → ℚ}
    (hx : r.holds x)
    (h : r.row.active (support x) → monomial r.row.lhs u = monomial r.row.rhs u) :
    r.holds (fun i => x i * u i) := by
  unfold MonomialTest.holds at *
  rw [monomial_mul, monomial_mul]
  by_cases ha : r.row.active (support x)
  · rw [h ha, hx, mul_assoc]
  · classical
    have hz : monomial r.row.lhs x = 0 ∨ monomial r.row.rhs x = 0 := by
      by_contra hn
      push_neg at hn
      apply ha
      intro i hi
      have xi : x i = 0 := by simpa using hi
      exact ⟨not_not.mp (fun h => hn.1 (monomial_eq_zero_of_factor _ xi h)),
        not_not.mp (fun h => hn.2 (monomial_eq_zero_of_factor _ xi h))⟩
    rcases hz with hl | hr
    · have hh : r.ratio * monomial r.row.rhs x = 0 := hx.symm.trans hl
      rw [← mul_assoc, hl, hh, zero_mul, zero_mul]
    · simpa [hr] using congrArg (fun a => a * monomial r.row.lhs u) hx

theorem balanced_of_endpoints (r : MonomialTest I) {x y u : I → ℚ}
    (hx : r.holds x) (hy : r.holds y)
    (hscale : y = fun i => x i * u i) (ha : r.row.active (support x)) :
    monomial r.row.lhs u = monomial r.row.rhs u := by
  unfold MonomialTest.holds at hx hy
  rw [hscale, monomial_mul, monomial_mul, ← mul_assoc, ← hx] at hy
  exact mul_left_cancel₀ (monomial_ne_zero_of_active ha).1 hy

end MovingProjection
