import MovingProjection.Local
import MovingProjection.LimitContraction
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! The signed support core is invariant under arbitrarily fine rational edits. -/

namespace MovingProjection

open Filter Set
open scoped Topology BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def codeSupport (s : I → SignType) : Finset I :=
  Finset.univ.filter fun i => s i ≠ 0

noncomputable def signCode (x : I → ℝ) : I → SignType :=
  fun i => SignType.sign (x i)

omit [DecidableEq I] in
theorem codeSupport_signCode (x : I → ℝ) : codeSupport (signCode x) = realSupport x := by
  ext i
  simp [codeSupport, signCode]

noncomputable def signedCore (rows : List (ExponentRow I)) (s : I → SignType) : I → SignType :=
  fun i => if i ∈ core rows (codeSupport s) then s i else 0

def realChart (tests : List (MonomialTest I)) (B : ℝ) (s : I → SignType) :
    Set (I → ℝ) :=
  {x | ‖x‖ ≤ B ∧ signCode x = s ∧
    ∀ r ∈ tests, realMonomial r.row.lhs x = (r.ratio : ℝ) * realMonomial r.row.rhs x}

omit [DecidableEq I] in
theorem realChart_closure_compact (tests : List (MonomialTest I)) (B : ℝ) (s : I → SignType) :
    IsCompact (closure (realChart tests B s)) := by
  have hsub : realChart tests B s ⊆ Metric.closedBall 0 B := by
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.1)
  exact (isCompact_closedBall (0 : I → ℝ) B).of_isClosed_subset
    isClosed_closure (closure_minimal hsub Metric.isClosed_closedBall)

private theorem retained_sign_of_limit {Y : Type*} {l : Filter Y} [l.NeBot]
    {f : Y → ℝ} {x : ℝ} {o : SignType} (h : Tendsto f l (𝓝 x))
    (hx : x ≠ 0) (ho : ∀ᶠ y in l, SignType.sign (f y) = o) :
    SignType.sign x = o := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · obtain ⟨y, hy, hey⟩ := (((tendsto_order.1 h).2 0 hn).and ho).exists
    exact (sign_neg hn).trans (sign_neg hy).symm |>.trans hey
  · obtain ⟨y, hy, hey⟩ := (((tendsto_order.1 h).1 0 hp).and ho).exists
    exact (sign_pos hp).trans (sign_pos hy).symm |>.trans hey

theorem signedCore_of_chart_limit {tests : List (MonomialTest I)} {s : I → SignType}
    {l : Filter (I → ℝ)} [l.NeBot] {x : I → ℝ}
    (hsign : ∀ᶠ a in l, signCode a = s)
    (hlim : ∀ i, Tendsto (fun a => a i) l (𝓝 (x i)))
    (htests : ∀ᶠ a in l, ∀ r ∈ tests,
      realMonomial r.row.lhs a = (r.ratio : ℝ) * realMonomial r.row.rhs a) :
    signedCore (tests.map MonomialTest.row) (signCode x) =
      signedCore (tests.map MonomialTest.row) s := by
  classical
  have hcontract := contracts_of_limit tests (l := l) id x (codeSupport s)
    (hs := hsign.mono fun a ha =>
      (codeSupport_signCode a).symm.trans (congrArg codeSupport ha)) hlim
    htests
  have hc := core_eq_of_reduces (Relation.ReflTransGen.single hcontract)
  unfold signedCore
  rw [codeSupport_signCode, ← hc]
  funext i
  by_cases hi : i ∈ core (tests.map MonomialTest.row) (codeSupport s)
  · have hsub : core (tests.map MonomialTest.row) (codeSupport s) ⊆ realSupport x :=
      (isCore_core _ _).2 _ (.single hcontract)
    simp only [if_pos hi]
    exact retained_sign_of_limit (hlim i) (mem_realSupport.mp (hsub hi))
      (hsign.mono fun _ h => congrFun h i)
  · simp [hi]

theorem signedCore_of_chart_closure {tests : List (MonomialTest I)} {B : ℝ} {s : I → SignType}
    {x : I → ℝ} (hx : x ∈ closure (realChart tests B s)) :
    signedCore (tests.map MonomialTest.row) (signCode x) =
      signedCore (tests.map MonomialTest.row) s := by
  let l := 𝓝[realChart tests B s] x
  haveI : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have hev : ∀ᶠ a in l, a ∈ realChart tests B s := self_mem_nhdsWithin
  exact signedCore_of_chart_limit (hev.mono fun _ h => h.2.1)
    (fun i => (continuous_apply i).continuousAt.continuousWithinAt)
    (hev.mono fun _ h => h.2.2)

def embed (x : I → ℚ) (i : I) : ℝ := x i

omit [DecidableEq I] in
theorem embed_mem_chart {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {B : ℝ} {x : I → ℚ} (hx : Legal tests budgets x) (hB : ‖embed x‖ ≤ B) :
    embed x ∈ realChart tests B (signCode (embed x)) := by
  refine ⟨hB, rfl, ?_⟩
  intro r hr
  change realMonomial r.row.lhs (fun i => (x i : ℝ)) =
    (r.ratio : ℝ) * realMonomial r.row.rhs (fun i => (x i : ℝ))
  rw [realMonomial_cast, realMonomial_cast]
  exact_mod_cast (show monomial r.row.lhs x = r.ratio * monomial r.row.rhs x from hx.1 r hr)

theorem fineConnected_signedCore {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y : I → ℚ}
    (hB : ∃ B : ℝ, ∀ a, Legal tests budgets a → ‖embed a‖ ≤ B)
    (h : FineConnected tests budgets x y) :
    signedCore (tests.map MonomialTest.row) (signCode (embed x)) =
      signedCore (tests.map MonomialTest.row) (signCode (embed y)) := by
  classical
  obtain ⟨B, hB⟩ := hB
  let key := signedCore (tests.map MonomialTest.row) (signCode (embed x))
  let root := signedCore (tests.map MonomialTest.row)
  let A : Set (I → ℝ) := ⋃ s : {s : I → SignType // root s = key}, closure (realChart tests B s)
  let C : Set (I → ℝ) := ⋃ s : {s : I → SignType // root s ≠ key}, closure (realChart tests B s)
  have hAc : IsCompact A := isCompact_iUnion fun s => realChart_closure_compact tests B s
  have hCc : IsCompact C := isCompact_iUnion fun s => realChart_closure_compact tests B s
  have hdis : Disjoint A C := by
    apply disjoint_left.2
    intro p hpa hpc
    obtain ⟨a, ha⟩ := mem_iUnion.1 hpa
    obtain ⟨c, hc⟩ := mem_iUnion.1 hpc
    have he : root a = root c :=
      (signedCore_of_chart_closure ha).symm.trans (signedCore_of_chart_closure hc)
    exact c.2 (he.symm.trans a.2)
  obtain ⟨δ, hδ, hgap⟩ := Metric.exists_pos_forall_lt_edist hAc hCc.isClosed hdis
  obtain ⟨ε, hε, hεδ⟩ := exists_rat_btwn (NNReal.coe_pos.mpr hδ : (0 : ℝ) < δ)
  have hεQ : (0 : ℚ) < ε := by exact_mod_cast hε
  have hstep (p q : I → ℚ) (hp : root (signCode (embed p)) = key)
      (hl : LocalStep tests budgets ε p q) : root (signCode (embed q)) = key := by
    by_contra hq
    have hpa : embed p ∈ A := mem_iUnion.2
      ⟨⟨_, hp⟩, subset_closure (embed_mem_chart hl.1 (hB p hl.1))⟩
    have hqc : embed q ∈ C := mem_iUnion.2
      ⟨⟨_, hq⟩, subset_closure (embed_mem_chart hl.2.1 (hB q hl.2.1))⟩
    have hd : dist (embed p) (embed q) < (ε : ℝ) := by
      apply (dist_pi_lt_iff hε).2
      intro i
      rw [Real.dist_eq]
      change |(p i : ℝ) - (q i : ℝ)| < (ε : ℝ)
      exact_mod_cast hl.2.2 i
    have hbad := hgap (embed p) hpa (embed q) hqc
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hbad
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (hd.trans hεδ).le)) hbad
  have hreach := h ε hεQ
  clear h
  have hfinal : root (signCode (embed y)) = key := by
    induction hreach with
    | refl => rfl
    | tail _ hl ih => exact hstep _ _ ih hl
  exact hfinal.symm

end MovingProjection
