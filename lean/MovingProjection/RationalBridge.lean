import MovingProjection.OneStateEvents
import Mathlib.NumberTheory.Real.Irrational

/-! The bounded arithmetic witness for the event reduction. The quadratic
condition rejects denominator zero over the rationals, while admitting an
exact rational choice of slack at every positive feasible denominator. -/

namespace MovingProjection.RationalBridge

open scoped BigOperators

theorem no_rational_sqrt_two (w : ℚ) (hw : 0 ≤ w) : w ^ 2 ≠ 2 := by
  intro he
  have hcast : (w : ℝ) ^ 2 = 2 := by exact_mod_cast he
  have hnonneg : (0 : ℝ) ≤ w := by exact_mod_cast hw
  have heq : (w : ℝ) = Real.sqrt 2 := by
    rw [← hcast, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
  exact irrational_sqrt_two ⟨w, heq⟩

theorem exists_bounded_slack {q : ℚ} (hq : 0 < q) (hq₁ : q ≤ 1) :
    ∃ w u : ℚ, 1 ≤ w ∧ w ≤ 2 ∧ |u| ≤ 1 ∧ w ^ 2 = 2 + q ^ 2 * u := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr₁ : (q : ℝ) ≤ 1 := by exact_mod_cast hq₁
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  have hs₁ : (1 : ℝ) < Real.sqrt 2 := by nlinarith
  have hs₂ : Real.sqrt 2 < (3 : ℝ) / 2 := by nlinarith
  have hspace : Real.sqrt 2 < Real.sqrt 2 + (q : ℝ) ^ 2 / 4 :=
    lt_add_of_pos_right _ (by positivity)
  obtain ⟨w, hlo, hhi⟩ := exists_rat_btwn hspace
  have hh : (w : ℝ) < 2 := by nlinarith
  have hprod : (w : ℝ) ^ 2 - 2 < (q : ℝ) ^ 2 := by
    calc
      _ = ((w : ℝ) - Real.sqrt 2) * ((w : ℝ) + Real.sqrt 2) := by nlinarith
      _ < ((q : ℝ) ^ 2 / 4) * 4 := by gcongr <;> linarith
      _ = _ := by ring
  have hpos : (0 : ℝ) ≤ (w : ℝ) ^ 2 - 2 := by nlinarith
  let u : ℚ := (w ^ 2 - 2) / q ^ 2
  have hq₂ : 0 < q ^ 2 := pow_pos hq _
  have hu : 0 ≤ u := div_nonneg (by exact_mod_cast hpos) hq₂.le
  have hu₁ : u ≤ 1 := by
    apply (div_le_one hq₂).2
    exact_mod_cast hprod.le
  refine ⟨w, u, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (hs₁.trans hlo).le
  · exact_mod_cast hh.le
  · rwa [abs_of_nonneg hu]
  · dsimp [u]
    field_simp
    ring

theorem bounded_witness_iff {I : Type*} [Fintype I]
    (polynomial : (I → ℚ) → ℚ) (homogeneous : ℚ → (I → ℚ) → ℚ)
    (hhom : ∀ q > 0, ∀ p, homogeneous q p = 0 ↔ polynomial (fun i => p i / q) = 0) :
    (∃ q : ℚ, ∃ p : I → ℚ, ∃ w u : ℚ,
      0 ≤ q ∧ q ≤ 1 ∧ (∀ i, |p i| ≤ 1) ∧ 1 ≤ w ∧ w ≤ 2 ∧ |u| ≤ 1 ∧
      w ^ 2 = 2 + q ^ 2 * u ∧ homogeneous q p = 0) ↔
      ∃ z, polynomial z = 0 := by
  constructor
  · rintro ⟨q, p, w, u, hq, _, _, hw, _, _, he, hp⟩
    have hq' : 0 < q := by
      by_contra! h
      have hz := le_antisymm h hq
      simp [hz] at he
      exact no_rational_sqrt_two w (by linarith) he
    exact ⟨_, (hhom q hq' p).mp hp⟩
  · rintro ⟨z, hz⟩
    classical
    let total : ℚ := ∑ i, |z i|
    have htotal : 0 ≤ total := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    let q : ℚ := 1 / (1 + total)
    have hq : 0 < q := by dsimp [q]; positivity
    have hq₁ : q ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    obtain ⟨w, u, hw, hw₂, hu, he⟩ := exists_bounded_slack hq hq₁
    let p : I → ℚ := fun i => q * z i
    refine ⟨q, p, w, u, hq.le, hq₁, fun i => ?_, hw, hw₂, hu, he, ?_⟩
    · have ht : |z i| ≤ total :=
        Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
      change |q * z i| ≤ 1
      rw [abs_mul, abs_of_pos hq]
      dsimp [q]
      rw [div_mul_eq_mul_div, one_mul]
      exact (div_le_one (by positivity)).2 (by linarith)
    · apply (hhom q hq p).mpr
      have hp : (fun i => p i / q) = z := by
        funext i
        change q * z i / q = z i
        field_simp
      rwa [hp]

end MovingProjection.RationalBridge
