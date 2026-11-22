import MovingProjection.PrimeInterpolation
import MovingProjection.Mesh
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.GroupWithZero

/-! Exact rational interpolation in a fixed signed chart, including active
per-mark budget boundaries. -/

namespace MovingProjection

open Filter Set
open scoped BigOperators Topology

variable {I : Type*} [Fintype I]

noncomputable def logSegment (x u : I → ℚ) (t : ℝ) : I → ℝ :=
  fun i => (x i : ℝ) * Real.exp (t * Real.log (u i : ℝ))

private theorem signs_equal_ratio {x y : ℚ}
    (h : SignType.sign (x : ℝ) = SignType.sign (y : ℝ)) (hx : x ≠ 0) :
    0 < y / x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have hxn : (x : ℝ) < 0 := by exact_mod_cast hn
    have hyn := sign_eq_neg_one_iff.mp (h.symm.trans (sign_neg hxn))
    exact div_pos_of_neg_of_neg (by exact_mod_cast hyn) hn
  · have hxp : 0 < (x : ℝ) := by exact_mod_cast hp
    have hyp := sign_eq_one_iff.mp (h.symm.trans (sign_pos hxp))
    exact div_pos (by exact_mod_cast hyp) hp

omit [Fintype I] in
private theorem sum_logSegment_lt (b : MarkBudget I) (x y u : I → ℚ)
    (hu : ∀ i, 0 < u i) (he : ∀ i, y i = x i * u i)
    (hx : ∑ i ∈ b.indices, |x i| ≤ b.cap)
    (hy : ∑ i ∈ b.indices, |y i| ≤ b.cap)
    (hchange : ∃ i ∈ b.indices, x i ≠ y i)
    {t : ℝ} (h₀ : 0 < t) (h₁ : t < 1) :
    (∑ i ∈ b.indices, |logSegment x u t i|) < (b.cap : ℝ) := by
  let bound (i : I) := (1-t) * |(x i : ℝ)| + t * |(y i : ℝ)|
  have ha (i : I) : |logSegment x u t i| ≤ bound i ∧
      (x i ≠ y i → |logSegment x u t i| < bound i) := by
    have huR : (0 : ℝ) < (u i : ℝ) := by exact_mod_cast hu i
    have heR : (y i : ℝ) = (x i : ℝ) * (u i : ℝ) := by exact_mod_cast he i
    have hle : Real.exp (t * Real.log (u i : ℝ)) ≤ (1-t) + t*(u i : ℝ) := by
      have h := convexOn_exp.2 (show (0 : ℝ) ∈ univ from mem_univ _)
        (show Real.log (u i : ℝ) ∈ univ from mem_univ _) (sub_nonneg.mpr h₁.le) h₀.le
        (show 1-t+t=1 by ring)
      simpa [smul_eq_mul, Real.exp_log huR] using h
    have hstrict (hne : u i ≠ 1) :
        Real.exp (t * Real.log (u i : ℝ)) < (1-t) + t*(u i : ℝ) := by
      have hlog : (0 : ℝ) ≠ Real.log (u i : ℝ) := by
        intro hzero
        have hh : (u i : ℝ) = 1 := by
          rw [← Real.exp_log huR, ← hzero, Real.exp_zero]
        exact hne (by exact_mod_cast hh)
      have h := strictConvexOn_exp.2 (show (0 : ℝ) ∈ univ from mem_univ _)
        (show Real.log (u i : ℝ) ∈ univ from mem_univ _) hlog (sub_pos.mpr h₁) h₀
        (show 1-t+t=1 by ring)
      simpa [smul_eq_mul, Real.exp_log huR] using h
    have habs :
        |(x i : ℝ)| * ((1-t) + t*(u i : ℝ)) = bound i := by
      unfold bound
      rw [heR, abs_mul, abs_of_pos huR]
      ring
    simp only [logSegment, abs_mul, Real.abs_exp]
    rw [← habs]
    refine ⟨mul_le_mul_of_nonneg_left hle (abs_nonneg _), fun hxy => ?_⟩
    have hxi : x i ≠ 0 := by
      intro he₀
      exact hxy (by rw [he i, he₀, zero_mul])
    have hui : u i ≠ 1 := by
      intro he₁
      exact hxy (by rw [he i, he₁, mul_one])
    exact mul_lt_mul_of_pos_left (hstrict hui) (abs_pos.mpr (by exact_mod_cast hxi))
  have H : (∑ i ∈ b.indices, |logSegment x u t i|) < ∑ i ∈ b.indices, bound i :=
    Finset.sum_lt_sum (fun i _ => (ha i).1) (by
      obtain ⟨i, hi, hn⟩ := hchange
      exact ⟨i, hi, (ha i).2 hn⟩)
  have hxR : (∑ i ∈ b.indices, |(x i : ℝ)|) ≤ (b.cap : ℝ) := by exact_mod_cast hx
  have hyR : (∑ i ∈ b.indices, |(y i : ℝ)|) ≤ (b.cap : ℝ) := by exact_mod_cast hy
  apply H.trans_le
  simp only [bound, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [(mul_le_mul_of_nonneg_left hxR (sub_nonneg.mpr h₁.le)),
    (mul_le_mul_of_nonneg_left hyR h₀.le)]

set_option maxHeartbeats 1000000 in
theorem fineConnected_same_chart {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y : I → ℚ} (hx : Legal tests budgets x) (hy : Legal tests budgets y)
    (hchart : signCode (embed x) = signCode (embed y)) :
    FineConnected tests budgets x y := by
  classical
  let u (i : I) := if x i = 0 then 1 else y i / x i
  have hs (i : I) : SignType.sign (x i : ℝ) = SignType.sign (y i : ℝ) := congrFun hchart i
  have hu (i : I) : 0 < u i := by
    by_cases h : x i = 0
    · simp [u, h]
    · simpa only [u, if_neg h] using signs_equal_ratio (hs i) h
  have he (i : I) : y i = x i * u i := by
    by_cases h : x i = 0
    · have hz : y i = 0 := by
        have H := sign_eq_zero_iff.mp ((hs i).symm.trans (by simp [h]))
        exact_mod_cast H
      simp [u, h, hz]
    · change y i = x i * (if x i = 0 then 1 else y i / x i)
      rw [if_neg h, ← mul_div_assoc, mul_div_cancel_left₀ _ h]
  let P := Finset.univ.biUnion (fun i => primesOf (u (i : I)))
  let z (i : I) (p : P) := padicValRat (p : ℕ) (u i)
  have hcontains (i : I) : primesOf (u i) ⊆ P := by
    intro p hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩
  have hprime (p : ℕ) (hp : p ∈ P) : Nat.Prime p := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_union.mp hi with hn | hd
    · exact Nat.prime_of_mem_primeFactors hn
    · exact Nat.prime_of_mem_primeFactors hd
  apply fineConnected_of_segment hx hy (f := logSegment x u)
  · unfold logSegment
    fun_prop
  · funext i
    simp [logSegment, embed]
  · funext i
    have hup : (0 : ℝ) < (u i : ℝ) := by exact_mod_cast hu i
    simp only [logSegment, one_mul, Real.exp_log hup, embed]
    exact_mod_cast (he i).symm
  · intro t ht
    rcases lt_or_eq_of_le ht.1 with h₀ | h₀
    · rcases lt_or_eq_of_le ht.2 with h₁ | h₁
      · apply Metric.mem_closure_iff.mpr
        intro ε hε
        let v₀ (p : P) := Real.exp (t * Real.log (p : ℕ))
        have hv₀ (p : P) : 0 < v₀ p := Real.exp_pos _
        let F (v : P → ℝ) (i : I) := (x i : ℝ) * realPrimeTransfer z v i
        have hF : F v₀ = logSegment x u t := by
          funext i
          unfold F logSegment
          congr 1
          have hpos : 0 < realPrimeTransfer z v₀ i := Finset.prod_pos fun p _ => zpow_pos (hv₀ p) _
          apply Real.log_injOn_pos hpos (Real.exp_pos _)
          rw [realPrimeTransfer_log z hv₀, Real.log_exp, log_rat_on (hu i) P (hcontains i) hprime]
          rw [← Finset.sum_coe_sort P (fun p => (padicValRat p (u i) : ℝ) * Real.log p)]
          simp only [v₀, Real.log_exp, Finset.mul_sum, z]
          apply Finset.sum_congr rfl
          intro p _
          ring
        have hcont : ContinuousAt F v₀ := by
          apply continuousAt_pi.mpr
          intro i
          apply continuousAt_const.mul
          exact tendsto_finset_prod _ fun p _ =>
            (continuous_apply p).continuousAt.zpow₀ _ (Or.inl (hv₀ p).ne')
        have hpositive : ∀ᶠ v in 𝓝 v₀, ∀ p, 0 < v p :=
          eventually_all.2 fun p => continuousAt_const.eventually_lt
            (continuous_apply p).continuousAt (hv₀ p)
        have hclose : ∀ᶠ v in 𝓝 v₀, dist (logSegment x u t) (F v) < ε := by
          have HH := hcont (Metric.ball_mem_nhds _ hε)
          filter_upwards [HH] with v hv
          rw [← hF, dist_comm]
          exact hv
        have hbounds : ∀ᶠ v in 𝓝 v₀, ∀ b : {b // b ∈ budgets},
            (∃ i ∈ b.1.indices, x i ≠ y i) →
            (∑ i ∈ b.1.indices, |F v i|) < (b.1.cap : ℝ) := by
          apply eventually_all.2
          intro b
          by_cases hb : ∃ i ∈ b.1.indices, x i ≠ y i
          · apply Filter.Eventually.mono ?_ (fun _ h _ => h)
            have H : ContinuousAt (fun v => ∑ i ∈ b.1.indices, |F v i|) v₀ :=
              tendsto_finset_sum _ fun i _ => ((continuousAt_pi.mp hcont) i).abs
            apply H.eventually_lt continuousAt_const
            rw [hF]
            exact sum_logSegment_lt b.1 x y u hu he (hx.2 _ b.2) (hy.2 _ b.2) hb h₀ h₁
          · exact Filter.Eventually.of_forall fun _ h => (hb h).elim
        have hd : DenseRange (fun q : P → ℚ => fun p => (q p : ℝ)) :=
          DenseRange.piMap (fun _ => Rat.isDenseEmbedding_coe_real.dense)
        obtain ⟨q, hpq, hqclose, hqb⟩ := hd.mem_nhds (hpositive.and (hclose.and hbounds))
        have hp (p : P) : 0 < q p := by
          have H := hpq p
          change 0 < (q p : ℝ) at H
          exact_mod_cast H
        let y' (i : I) := x i * primeTransfer z q i
        refine ⟨embed y', ⟨y', ⟨?_, ?_⟩, rfl⟩, ?_⟩
        · intro r hr
          apply MonomialTest.holds_mul_positive r (hx.1 r hr)
          intro ha
          exact primeTransfer_monomial z hp r.row (fun p =>
            valuation_balanced (hprime p p.2) r u (fun i => (hu i).ne')
              (balanced_of_endpoints r (hx.1 r hr) (hy.1 r hr) (funext he) ha))
        · intro b hb
          by_cases hdiff : ∃ i ∈ b.indices, x i ≠ y i
          · have H := (hqb ⟨b,hb⟩ hdiff).le
            simp only [F, realPrimeTransfer_cast, ← Rat.cast_mul] at H
            exact_mod_cast H
          · refine (le_of_eq ?_).trans (hx.2 b hb)
            apply Finset.sum_congr rfl
            intro i hi
            have hi' : x i = y i := by
              by_contra hn
              exact hdiff ⟨i, hi, hn⟩
            have hui : u i = 1 := by
              by_cases hz : x i = 0
              · simp [u, hz]
              · simp [u, hz, ← hi']
            simp [y', primeTransfer, z, hui]
        · have hfun : F (fun p => (q p : ℝ)) = embed y' := by
            funext i
            simp [F, embed, y', realPrimeTransfer_cast]
          exact hfun ▸ hqclose
      · subst t
        apply subset_closure
        refine ⟨y, hy, ?_⟩
        funext i
        have hup : (0 : ℝ) < (u i : ℝ) := by exact_mod_cast hu i
        simp only [logSegment, one_mul, Real.exp_log hup, embed]
        exact_mod_cast he i
    · subst t
      apply subset_closure
      exact ⟨x, hx, by funext i; simp [logSegment, embed]⟩

end MovingProjection
