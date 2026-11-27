import MovingProjection.Classification
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Connected.PathConnected

/-! Components of the full real lawful locus, with no boundedness assumption. -/

namespace MovingProjection

open Filter Set
open scoped Topology BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def RealLegal (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (x : I → ℝ) : Prop :=
  (∀ r ∈ tests, realMonomial r.row.lhs x = (r.ratio : ℝ) * realMonomial r.row.rhs x) ∧
    ∀ b ∈ budgets, ∑ i ∈ b.indices, |x i| ≤ (b.cap : ℝ)

omit [DecidableEq I] in
theorem realLegal_embed {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℚ} (hx : Legal tests budgets x) : RealLegal tests budgets (embed x) := by
  refine ⟨?_, ?_⟩
  · exact (embed_mem_chart hx le_rfl).2.2
  · intro b hb
    change (∑ i ∈ b.indices, |(x i : ℝ)|) ≤ (b.cap : ℝ)
    exact_mod_cast hx.2 b hb

omit [DecidableEq I] in
theorem isClosed_realLegal (tests : List (MonomialTest I)) (budgets : List (MarkBudget I)) :
    IsClosed {x | RealLegal tests budgets x} := by
  unfold RealLegal
  simp only [setOf_and, setOf_forall]
  apply IsClosed.inter
  · refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_eq ?_ ?_
    all_goals unfold realMonomial; fun_prop
  · refine isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop

theorem signedCore_of_real_chart_closure {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {s : I → SignType} {x : I → ℝ}
    (hx : x ∈ closure {a | RealLegal tests budgets a ∧ signCode a = s}) :
    signedCore (tests.map MonomialTest.row) (signCode x) =
      signedCore (tests.map MonomialTest.row) s := by
  let chart := {a | RealLegal tests budgets a ∧ signCode a = s}
  let l := 𝓝[chart] x
  haveI : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have h : ∀ᶠ a in l, a ∈ chart := self_mem_nhdsWithin
  exact signedCore_of_chart_limit (h.mono fun _ ha => ha.2)
    (fun i => (continuous_apply i).continuousAt.continuousWithinAt)
    (h.mono fun _ ha => ha.1.1)

private theorem isClosed_real_core (tests : List (MonomialTest I)) (budgets : List (MarkBudget I))
    (accept : (I → SignType) → Prop) :
    IsClosed {x | RealLegal tests budgets x ∧
      accept (signedCore (tests.map MonomialTest.row) (signCode x))} := by
  classical
  let root := signedCore (tests.map MonomialTest.row)
  let chart (s : I → SignType) := {x | RealLegal tests budgets x ∧ signCode x = s}
  have heq : {x | RealLegal tests budgets x ∧ accept (root (signCode x))} =
      ⋃ s : {s // accept (root s)}, closure (chart s) := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨⟨signCode x, hx.2⟩, subset_closure ⟨hx.1, rfl⟩⟩
    · intro hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      refine ⟨closure_minimal (fun _ h => h.1) (isClosed_realLegal tests budgets) hs, ?_⟩
      change accept (signedCore (tests.map MonomialTest.row) (signCode x))
      rw [signedCore_of_real_chart_closure hs]
      exact s.2
  change IsClosed {x | RealLegal tests budgets x ∧ accept (root (signCode x))}
  rw [heq]
  exact isClosed_iUnion_of_finite fun _ => isClosed_closure

theorem real_connectedComponent_signedCore {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℝ}
    (hy : y ∈ connectedComponentIn {a | RealLegal tests budgets a} x) :
    signedCore (tests.map MonomialTest.row) (signCode x) =
      signedCore (tests.map MonomialTest.row) (signCode y) := by
  let root (a : I → ℝ) := signedCore (tests.map MonomialTest.row) (signCode a)
  let F := {a | RealLegal tests budgets a}
  let A := {a ∈ F | root a = root x}
  let C := {a ∈ F | root a ≠ root x}
  have hA : IsClosed A := isClosed_real_core tests budgets (· = root x)
  have hC : IsClosed C := isClosed_real_core tests budgets (· ≠ root x)
  have hsub := connectedComponentIn_subset F x
  have hx := (connectedComponentIn_nonempty_iff.mp ⟨y, hy⟩)
  by_contra hne
  have hs := isPreconnected_closed_iff.mp (isPreconnected_connectedComponentIn (x := x) (F := F))
    A C hA hC (fun a ha => by
      by_cases he : root a = root x
      · exact Or.inl ⟨hsub ha, he⟩
      · exact Or.inr ⟨hsub ha, he⟩)
    ⟨x, mem_connectedComponentIn hx, hx, rfl⟩ ⟨y, hy, hsub hy, Ne.symm hne⟩
  obtain ⟨z, _, hzA, hzC⟩ := hs
  exact hzC.2 hzA.2

omit [DecidableEq I] in
private theorem realMonomial_mul (e : I → ℕ) (x f : I → ℝ) :
    realMonomial e (fun i => x i * f i) = realMonomial e x * realMonomial e f := by
  simp [realMonomial, mul_pow, Finset.prod_mul_distrib]

omit [DecidableEq I] in
private theorem realMonomial_zero_of_factor {e : I → ℕ} {x : I → ℝ} {i : I}
    (hx : x i = 0) (he : e i ≠ 0) : realMonomial e x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hx, zero_pow he])

omit [DecidableEq I] in
private theorem active_of_nonzero {r : MonomialTest I} {x : I → ℝ}
    (hx : realMonomial r.row.lhs x = (r.ratio : ℝ) * realMonomial r.row.rhs x)
    (hn : realMonomial r.row.lhs x ≠ 0) : r.row.active (realSupport x) := by
  intro i hi
  have hz : x i = 0 := by simpa using hi
  have hr : realMonomial r.row.rhs x ≠ 0 := (mul_ne_zero_iff.mp (hx ▸ hn)).2
  exact ⟨not_not.mp (fun he => hn (realMonomial_zero_of_factor hz he)),
    not_not.mp (fun he => hr (realMonomial_zero_of_factor hz he))⟩

omit [DecidableEq I] in
private theorem real_legal_of_mul {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x f : I → ℝ} (hx : RealLegal tests budgets x)
    (hfactor : ∀ r ∈ tests, r.row.active (realSupport x) →
      realMonomial r.row.lhs f = realMonomial r.row.rhs f)
    (hguards : ∀ b ∈ budgets, ∑ i ∈ b.indices, |x i * f i| ≤ (b.cap : ℝ)) :
    RealLegal tests budgets (fun i => x i * f i) := by
  refine ⟨fun r hr => ?_, hguards⟩
  have ht := hx.1 r hr
  rw [realMonomial_mul, realMonomial_mul, ← mul_assoc, ← ht]
  by_cases hn : realMonomial r.row.lhs x = 0
  · simp [hn]
  · rw [hfactor r hr (active_of_nonzero ht hn)]

omit [DecidableEq I] in
private theorem real_contract_path {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℝ} (hx : RealLegal tests budgets x)
    {S : Finset I} (h : Contracts (tests.map MonomialTest.row) (realSupport x) S) :
    ∃ y, RealLegal tests budgets y ∧
      JoinedIn {a | RealLegal tests budgets a} x y ∧
      realSupport y = S ∧ ∀ i ∈ S, y i = x i := by
  obtain ⟨w, hw, rfl⟩ := h
  let f (t : ℝ) (i : I) := x i * t ^ w i
  have h₀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : RealLegal tests budgets (f t) := by
    apply real_legal_of_mul hx
    · intro r hr ha
      simp only [realMonomial, ← pow_mul, Nat.mul_comm (w _), Finset.prod_pow_eq_pow_sum]
      rw [hw.2 r.row (List.mem_map_of_mem hr) ha]
    · intro b hb
      apply le_trans _ (hx.2 b hb)
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht.1 ht.2)
  have h1 : f 1 = x := by funext i; simp [f]
  refine ⟨f 0, h₀ 0 ⟨le_rfl, zero_le_one⟩, ?_, ?_, ?_⟩
  · rw [← h1]
    exact (JoinedIn.ofLine (by dsimp [f]; fun_prop) rfl rfl
      (fun _ ⟨t, ht, h⟩ => h ▸ h₀ t ht)).symm
  · ext i
    by_cases hi : w i = 0 <;> simp [f, hi, zero_pow]
  · intro i hi
    simp [f, (Finset.mem_filter.mp hi).2]

private theorem real_to_core {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x : I → ℝ} (hx : RealLegal tests budgets x) :
    ∃ y, RealLegal tests budgets y ∧
      JoinedIn {a | RealLegal tests budgets a} x y ∧
      signCode y = signedCore (tests.map MonomialTest.row) (signCode x) := by
  let rows := tests.map MonomialTest.row
  let S := realSupport x
  have hred := (isCore_core rows S).1
  have hpure (T : Finset I) (hT : Reduces rows S T) :
      ∃ y, RealLegal tests budgets y ∧
        JoinedIn {a | RealLegal tests budgets a} x y ∧ realSupport y = T ∧
          ∀ i ∈ T, y i = x i := by
    induction hT with
    | refl => exact ⟨x, hx, JoinedIn.refl hx, rfl, fun _ _ => rfl⟩
    | @tail U T _ h ih =>
      obtain ⟨u, hu, hxu, hsu, hval⟩ := ih
      have h' := real_contract_path hu (hsu.symm ▸ h)
      obtain ⟨v, hv, huv, hsv, hvval⟩ := h'
      refine ⟨v, hv, hxu.trans huv, hsv, fun i hi => (hvval i hi).trans ?_⟩
      exact hval i (h.subset hi)
  obtain ⟨y, hy, hxy, hys, hval⟩ := hpure _ hred
  refine ⟨y, hy, hxy, ?_⟩
  unfold signedCore
  rw [codeSupport_signCode, ← hys]
  funext i
  by_cases hi : i ∈ realSupport y
  · simp [hi, signCode, hval i (hys ▸ hi)]
  · have hzero : y i = 0 := by simpa using hi
    simp [hi, signCode, hzero]

omit [DecidableEq I] in
private theorem real_same_chart_path {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℝ}
    (hx : RealLegal tests budgets x) (hy : RealLegal tests budgets y) (hs : signCode x = signCode y) :
    JoinedIn {a | RealLegal tests budgets a} x y := by
  let f (t : ℝ) (i : I) := Real.exp (t * (Real.log (y i) - Real.log (x i)))
  let z (t : ℝ) (i : I) := x i * f t i
  have he (i : I) : SignType.sign (x i) = SignType.sign (y i) := congrFun hs i
  have hyz (i : I) : x i = 0 ↔ y i = 0 := by
    rw [← (sign_eq_zero_iff (a := x i)), ← (sign_eq_zero_iff (a := y i)), he i]
  have hmag (t : ℝ) (i : I) (hxi : x i ≠ 0) :
      |z t i| = Real.exp ((1 - t) * Real.log (x i) + t * Real.log (y i)) := by
    change |x i * Real.exp (t * (Real.log (y i) - Real.log (x i)))| = _
    rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_log_eq_abs hxi, ← Real.exp_add]
    congr 1
    ring
  have hz (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : RealLegal tests budgets (z t) := by
    apply real_legal_of_mul hx
    · intro r hr ha
      have hsame : realSupport x = realSupport y := by rw [← codeSupport_signCode, ← codeSupport_signCode, hs]
      have hxx := log_equation r x ha (hx.1 r hr)
      have hyy := log_equation r y (hsame ▸ ha) (hy.1 r hr)
      have hexp (e : I → ℕ) :
          realMonomial e (f t) =
            Real.exp (t * ((∑ i, (e i : ℝ) * Real.log (y i)) -
              (∑ i, (e i : ℝ) * Real.log (x i)))) := by
        simp only [realMonomial, f, ← Real.exp_nat_mul, ← Real.exp_sum]
        congr 1
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hexp, hexp]
      congr 1
      simp only [sub_mul, Finset.sum_sub_distrib] at hxx hyy
      linear_combination t * (hyy - hxx)
    · intro b hb
      calc
        _ ≤ ∑ i ∈ b.indices, ((1 - t) * |x i| + t * |y i|) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hxi : x i = 0
          · simp [hxi, (hyz i).mp hxi]
          · have hyi : y i ≠ 0 := mt (hyz i).mpr hxi
            rw [hmag t i hxi, ← Real.exp_log_eq_abs hxi, ← Real.exp_log_eq_abs hyi]
            exact convexOn_exp.2 (mem_univ (Real.log (x i))) (mem_univ (Real.log (y i)))
              (sub_nonneg.mpr ht.2) ht.1 (by ring)
        _ = (1 - t) * (∑ i ∈ b.indices, |x i|) + t * (∑ i ∈ b.indices, |y i|) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ (1 - t) * (b.cap : ℝ) + t * (b.cap : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2 b hb) (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left (hy.2 b hb) ht.1)
        _ = (b.cap : ℝ) := by ring
  have h0 : z 0 = x := by funext i; simp [z, f]
  have h1 : z 1 = y := by
    funext i
    by_cases hxi : x i = 0
    · simp [z, hxi, (hyz i).mp hxi]
    · have hyi : y i ≠ 0 := mt (hyz i).mpr hxi
      calc
        z 1 i = (SignType.sign (x i) : ℝ) * |z 1 i| := by
          change x i * f 1 i = _
          rw [show |z 1 i| = |x i| * f 1 i by
            change |x i * f 1 i| = _
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]]
          rw [← mul_assoc, sign_mul_abs]
        _ = y i := by
          rw [he i, hmag 1 i hxi]
          simp [Real.exp_log_eq_abs hyi, sign_mul_abs]
  exact JoinedIn.ofLine (by dsimp [z, f]; fun_prop) h0 h1
    (fun _ ⟨t, ht, h⟩ => h ▸ hz t ht)

theorem real_joinedIn_iff_signedCore {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℝ}
    (hx : RealLegal tests budgets x) (hy : RealLegal tests budgets y) :
    JoinedIn {a | RealLegal tests budgets a} x y ↔
      signedCore (tests.map MonomialTest.row) (signCode x) =
        signedCore (tests.map MonomialTest.row) (signCode y) := by
  constructor
  · rintro ⟨p, hp⟩
    have hconn := isPreconnected_range p.continuous
    exact real_connectedComponent_signedCore
      (hconn.subset_connectedComponentIn p.source_mem_range (range_subset_iff.mpr hp)
        p.target_mem_range)
  · intro h
    obtain ⟨u, hu, hxu, huc⟩ := real_to_core hx
    obtain ⟨v, hv, hyv, hvc⟩ := real_to_core hy
    exact hxu.trans ((real_same_chart_path hu hv (huc.trans (h.trans hvc.symm))).trans hyv.symm)

theorem real_connectedComponent_iff_signedCore {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℝ}
    (hx : RealLegal tests budgets x) (hy : RealLegal tests budgets y) :
    y ∈ connectedComponentIn {a | RealLegal tests budgets a} x ↔
      signedCore (tests.map MonomialTest.row) (signCode x) =
        signedCore (tests.map MonomialTest.row) (signCode y) := by
  refine ⟨real_connectedComponent_signedCore, fun h => ?_⟩
  obtain ⟨p, hp⟩ := (real_joinedIn_iff_signedCore hx hy).mpr h
  exact (isPreconnected_range p.continuous).subset_connectedComponentIn
    p.source_mem_range (range_subset_iff.mpr hp) p.target_mem_range

theorem fineConnected_iff_real_joinedIn {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℚ}
    (hx : Legal tests budgets x) (hy : Legal tests budgets y)
    (hbound : ∃ B : ℝ, ∀ a, Legal tests budgets a → ‖embed a‖ ≤ B) :
    FineConnected tests budgets x y ↔
      JoinedIn {a | RealLegal tests budgets a} (embed x) (embed y) :=
  (fineConnected_iff_signedCore hx hy hbound).trans
    (real_joinedIn_iff_signedCore (realLegal_embed hx) (realLegal_embed hy)).symm

end MovingProjection
