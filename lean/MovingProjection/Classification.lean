import MovingProjection.ChartPath

/-! Exact classification of rational numerical locality by signed cores. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem core_representative_sign {rows : List (ExponentRow I)}
    {x y : I → ℚ} (hs : support y = core rows (support x))
    (h : ∀ i ∈ support y, y i = x i) :
    signCode (embed y) = signedCore rows (signCode (embed x)) := by
  have he : codeSupport (signCode (embed x)) = support x :=
    (codeSupport_signCode _).trans (realSupport_cast x)
  funext i
  unfold signedCore
  rw [he, ← hs]
  by_cases hi : i ∈ support y
  · simp [hi, signCode, embed, h i hi]
  · have hzero : y i = 0 := by simpa using hi
    simp [hi, signCode, embed, hzero]

theorem fineConnected_iff_signedCore {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℚ}
    (hx : Legal tests budgets x) (hy : Legal tests budgets y)
    (hbound : ∃ B : ℝ, ∀ a, Legal tests budgets a → ‖embed a‖ ≤ B) :
    FineConnected tests budgets x y ↔
      signedCore (tests.map MonomialTest.row) (signCode (embed x)) =
        signedCore (tests.map MonomialTest.row) (signCode (embed y)) := by
  constructor
  · exact fineConnected_signedCore hbound
  · intro h
    obtain ⟨u, hu, hxu, hsu, hval⟩ := fineConnected_to_core hx
    obtain ⟨v, hv, hyv, hsv, hvval⟩ := fineConnected_to_core hy
    have he := (core_representative_sign hsu hval).trans
      (h.trans (core_representative_sign hsv hvval).symm)
    exact hxu.trans ((fineConnected_same_chart hu hv he).trans hyv.symm)

omit [DecidableEq I] in
theorem bounded_of_budget_cover {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)}
    (hcover : ∀ i, ∃ b ∈ budgets, i ∈ b.indices) :
    ∃ B : ℝ, ∀ a, Legal tests budgets a → ‖embed a‖ ≤ B := by
  classical
  choose budget hb hindex using hcover
  let B : ℚ := ∑ i, |(budget i).cap|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨(B : ℝ), fun a ha => ?_⟩
  rw [← dist_zero_right]
  apply (dist_pi_le_iff (by exact_mod_cast hB : (0 : ℝ) ≤ (B : ℝ))).2
  intro i
  rw [Real.dist_eq]
  change |(a i : ℝ) - 0| ≤ (B : ℝ)
  rw [sub_zero]
  have hsingle : |a i| ≤ ∑ j ∈ (budget i).indices, |a j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (hindex i)
  have hcap : |(budget i).cap| ≤ B :=
    Finset.single_le_sum (fun j _ => abs_nonneg (budget j).cap) (Finset.mem_univ i)
  exact_mod_cast (hsingle.trans ((ha.2 _ (hb i)).trans ((le_abs_self _).trans hcap)))

end MovingProjection
