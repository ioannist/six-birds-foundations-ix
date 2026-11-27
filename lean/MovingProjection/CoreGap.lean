import MovingProjection.CoreCertificate

/-! The metric step of the quantitative obstruction. A uniform lower bound
for survivor magnitudes gives a separation bound in the same norm. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem signedCore_eq_of_survivors_separated {rows : List (ExponentRow I)} {η : ℚ}
    {x y : I → ℚ}
    (hx : ∀ i ∈ core rows (support x), η ≤ |x i|)
    (hy : ∀ i ∈ core rows (support y), η ≤ |y i|)
    (hclose : ∀ i, |x i - y i| < η) :
    signedCore rows (signCode (embed x)) = signedCore rows (signCode (embed y)) := by
  let cx := core rows (support x)
  let cy := core rows (support y)
  let common := support x ∩ support y
  have hxcore : IsCore rows (support x) cx := isCore_core _ _
  have hycore : IsCore rows (support y) cy := isCore_core _ _
  have hxy : ∀ i ∈ cx, i ∈ support y := by
    intro i hi
    rw [mem_support]
    intro hz
    have h := hclose i
    rw [hz, sub_zero] at h
    exact (not_lt_of_ge (hx i hi)) h
  have hyx : ∀ i ∈ cy, i ∈ support x := by
    intro i hi
    rw [mem_support]
    intro hz
    have h := hclose i
    rw [abs_sub_comm, hz, sub_zero] at h
    exact (not_lt_of_ge (hy i hi)) h
  have hcx : cx ⊆ common := fun i hi => Finset.mem_inter.mpr ⟨hxcore.1.subset hi, hxy i hi⟩
  have hcy : cy ⊆ common := fun i hi => Finset.mem_inter.mpr ⟨hyx i hi, hycore.1.subset hi⟩
  have hstepx := hxcore.1.restrict (u := common) Finset.inter_subset_left
  have hstepy := hycore.1.restrict (u := common) Finset.inter_subset_right
  rw [Finset.inter_eq_right.mpr hcx] at hstepx
  rw [Finset.inter_eq_right.mpr hcy] at hstepy
  have heq : cx = cy := by
    have hx' := (core_eq_of_reduces hstepx).symm.trans (core_eq_of_reduces hstepy)
    exact ((hxcore.of_reduces hxcore.1).unique (isCore_core rows cx)).trans
      (hx'.trans ((hycore.of_reduces hycore.1).unique (isCore_core rows cy)).symm)
  apply (CoreCertificate.signedCore_eq_iff hxcore hycore).mpr
  refine ⟨heq, fun i hi => ?_⟩
  have hix : x i ≠ 0 := mem_support.mp (hxcore.1.subset hi)
  have hfar := hx i hi
  have hnear := abs_lt.mp (hclose i)
  rcases lt_or_gt_of_ne hix with hneg | hpos
  · rw [abs_of_neg hneg] at hfar
    have hyneg : ¬ 0 < y i := by intro hp; linarith [hnear.1]
    simp [not_lt_of_gt hneg, hyneg]
  · rw [abs_of_pos hpos] at hfar
    have hypos : 0 < y i := by linarith [hnear.2]
    simp [hpos, hypos]

theorem signedCore_eq_of_bounded_mesh {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {η : ℚ} {x y : I → ℚ}
    (hgap : ∀ a, Legal tests budgets a →
      ∀ i ∈ core (tests.map MonomialTest.row) (support a), η ≤ |a i|)
    (h : Relation.ReflTransGen (LocalStep tests budgets η) x y) :
    signedCore (tests.map MonomialTest.row) (signCode (embed x)) =
      signedCore (tests.map MonomialTest.row) (signCode (embed y)) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    exact ih.trans (signedCore_eq_of_survivors_separated
      (hgap _ hstep.1) (hgap _ hstep.2.1) hstep.2.2)

theorem Protocol.signature_eq_of_bounded_mesh
    {M X R Γ Δ : Type*} {n : ℕ} [Fintype M] [Fintype X] [Fintype R]
    [Fintype Γ] [Fintype Δ] [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R]
    (D : Protocol M I X R Γ Δ) {a b : D.State n} {η : ℚ} (hη : 0 < η)
    (hgap : ∀ x, Legal (D.fiber a.profile).spectralChecks (spectrumBudgets D.κ) x →
      ∀ i ∈ core ((D.fiber a.profile).spectralChecks.map MonomialTest.row) (support x), η ≤ |x i|)
    (h : D.Chain (D.δ * η / (2 * (Fintype.card (X × R) : ℚ) + 1)) a b) :
    D.signature a.profile a.law = D.signature a.profile b.law := by
  apply signedCore_eq_of_bounded_mesh hgap
  induction h with
  | refl => exact .refl
  | @tail y z hy hs ih =>
    obtain ⟨e, he⟩ := hs
    by_cases he' : e = .rewrite
    · subst e
      obtain ⟨hp, hnear⟩ : y.profile = z.profile ∧ PhysicalNear D.kernel _ y.law z.law := by
        simpa [Protocol.Step] using he
      have hstep : (D.fiber y.profile).step D.δ D.κ D.ν D.reverse D.kernel _ y.law z.law :=
        ⟨y.legal.2.2, hp ▸ z.legal.2.2, hnear⟩
      have hloc := spectralModulus_for_physicalStep (R := R) D.kernel D.δ_pos D.κ_lt_one hη
        (p := D.fiber y.profile) (ν := D.ν) (rev := D.reverse) (a := y.law) (c := z.law)
        (by simpa only [Fintype.card_prod, Nat.cast_mul] using hstep)
      have hle := Capabilities.le_coordinates.mp (Protocol.Chain.profile_le hy)
      have hin := D.checks.spectralTests_mono hle.2.2.1 hle.2.2.2
      exact ih.tail ⟨⟨fun r hr => hloc.1.1 r (hin hr), hloc.1.2⟩,
        ⟨fun r hr => hloc.2.1.1 r (hin hr), hloc.2.1.2⟩, hloc.2.2⟩
    · rwa [← he.spectrum_eq he']

/-- The exact log identity read by an integer dual certificate of a lawful
support. Coefficients of inactive tests do not enter the identity. -/
theorem CoreCertificate.dual_log_identity {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x : I → ℚ} (hx : Legal tests budgets x)
    (multipliers : Fin (tests.map MonomialTest.row).length → ℤ) :
    ∑ i, (dualCoordinate (tests.map MonomialTest.row) (support x) multipliers i : ℝ) *
      Real.log (x i : ℝ) =
    ∑ k, if activeCheck ((tests.map MonomialTest.row)[k]) (support x) then
      (multipliers k : ℝ) * Real.log ((tests[k]'(by simpa using k.isLt)).ratio : ℝ) else 0 := by
  simp only [dualCoordinate, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hactive : activeCheck ((tests.map MonomialTest.row)[k]) (support x) = true
  · let test := tests[k]'(by simpa using k.isLt)
    have hrow : (tests.map MonomialTest.row)[k] = test.row := by simp [test]
    have hsupport : realSupport (embed x) = support x := realSupport_cast x
    have ha : test.row.active (realSupport (embed x)) := by
      rw [hsupport, ← hrow]
      exact activeCheck_eq_true.mp hactive
    have htest : test.holds x := hx.1 test (List.getElem_mem _)
    have heq : realMonomial test.row.lhs (embed x) =
        (test.ratio : ℝ) * realMonomial test.row.rhs (embed x) := by
      change realMonomial test.row.lhs (fun i => (x i : ℝ)) =
        (test.ratio : ℝ) * realMonomial test.row.rhs (fun i => (x i : ℝ))
      rw [realMonomial_cast, realMonomial_cast, htest]
      norm_cast
    have hlog := log_equation test (embed x) ha heq
    change (∑ i, ((test.row.lhs i : ℝ) - (test.row.rhs i : ℝ)) *
      Real.log (x i : ℝ)) = Real.log (test.ratio : ℝ) at hlog
    rw [hrow] at hactive ⊢
    simp only [if_pos hactive, Int.cast_mul, Int.cast_sub, Int.cast_natCast, mul_assoc]
    rw [← Finset.mul_sum, hlog]
  · simp only [if_neg hactive, Int.cast_zero, zero_mul, Finset.sum_const_zero]

/-- The numerical survivor estimate from a checked terminal certificate.
The radius and multiplier bounds are supplied as real inequalities here. -/
theorem CoreCertificate.dual_survivor_lower {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x : I → ℚ} (hx : Legal tests budgets x)
    {R B V : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (multipliers : Fin (tests.map MonomialTest.row).length → ℤ)
    (hterminal : terminalCheck (tests.map MonomialTest.row) (support x) multipliers = true)
    (hV : ∀ i, (dualCoordinate (tests.map MonomialTest.row) (support x) multipliers i : ℝ) ≤ V)
    (hlog : ∀ i, Real.log (x i : ℝ) ≤ R)
    (hcoeff : -B ≤ ∑ k, if activeCheck ((tests.map MonomialTest.row)[k]) (support x) then
      (multipliers k : ℝ) * Real.log ((tests[k]'(by simpa using k.isLt)).ratio : ℝ) else 0)
    (i : I) (hi : i ∈ support x) :
    Real.exp (-B - Fintype.card I * V * R) ≤ |(x i : ℝ)| := by
  let v (j : I) : ℝ := dualCoordinate (tests.map MonomialTest.row) (support x) multipliers j
  have hpos : ∀ j ∈ support x, 0 < dualCoordinate (tests.map MonomialTest.row)
      (support x) multipliers j := of_decide_eq_true hterminal
  have hv (j : I) : 0 ≤ v j := by
    by_cases hj : j ∈ support x
    · dsimp only [v]
      exact_mod_cast (hpos j hj).le
    · unfold v dualCoordinate
      simp only [Int.cast_sum]
      apply Finset.sum_nonneg
      intro k _
      by_cases hk : activeCheck ((tests.map MonomialTest.row)[k]) (support x) = true
      · have hz := (activeCheck_eq_true.mp hk) j hj
        simp only [hk, if_true, hz.1, hz.2, Nat.cast_zero, sub_self, mul_zero, Int.cast_zero, le_refl]
      · simp only [hk, Bool.false_eq_true, if_false, Int.cast_zero, le_refl]
  have hv1 : 1 ≤ v i := by
    have hh : 1 ≤ dualCoordinate (tests.map MonomialTest.row) (support x) multipliers i := by
      have := hpos i hi
      omega
    dsimp only [v]
    exact_mod_cast hh
  have hVR : 0 ≤ V * R := mul_nonneg ((hv i).trans (hV i)) hR
  have hsum : (∑ j ∈ (Finset.univ.erase i), v j * Real.log (x j : ℝ)) ≤
      Fintype.card I * V * R := by
    calc
      _ ≤ ∑ _j ∈ (Finset.univ.erase i), V * R := Finset.sum_le_sum (fun j _ =>
        (mul_le_mul_of_nonneg_left (hlog j) (hv j)).trans
          (mul_le_mul_of_nonneg_right (hV j) hR))
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by
          exact_mod_cast Finset.card_le_univ (Finset.univ.erase i)) hVR
  rw [← dual_log_identity hx multipliers] at hcoeff
  change -B ≤ ∑ j, v j * Real.log (x j : ℝ) at hcoeff
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hcoeff
  have hlogi : -B - Fintype.card I * V * R ≤ Real.log (x i : ℝ) := by
    by_contra! hc
    have hn : 0 ≤ (Fintype.card I : ℝ) * V * R := by
      rw [mul_assoc]
      positivity
    have hl : Real.log (x i : ℝ) < 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_right hv1 hl.le
    rw [one_mul] at hmul
    linarith
  have hix : (x i : ℝ) ≠ 0 := by exact_mod_cast mem_support.mp hi
  rw [← Real.log_abs (x i : ℝ)] at hlogi
  exact (Real.le_log_iff_exp_le (abs_pos.mpr hix)).mp hlogi

end MovingProjection
