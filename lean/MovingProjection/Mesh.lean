import MovingProjection.Components
import Mathlib.Topology.Order.IntermediateValue

/-! A connected path in the closure of lawful rational points gives finite
chains of lawful rational steps at every tolerance. -/

namespace MovingProjection

open Filter Set

variable {I : Type*} [Fintype I]

theorem fineConnected_of_preconnected {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℚ} (hx : Legal tests budgets x)
    (hy : Legal tests budgets y) {S : Set (I → ℝ)} (hconn : IsPreconnected S)
    (ha : embed x ∈ S) (hb : embed y ∈ S)
    (hS : S ⊆ closure (embed '' {q | Legal tests budgets q})) :
    FineConnected tests budgets x y := by
  intro ε hε
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  by_contra hn
  let reach (q : I → ℚ) := Relation.ReflTransGen (LocalStep tests budgets ε) x q
  let A := ⋃ q : {q : I → ℚ // Legal tests budgets q ∧ reach q},
    Metric.ball (embed q.1) ((ε : ℝ)/3)
  let B := ⋃ q : {q : I → ℚ // Legal tests budgets q ∧ ¬ reach q},
    Metric.ball (embed q.1) ((ε : ℝ)/3)
  have hr : 0 < (ε : ℝ)/3 := by positivity
  have hcover : S ⊆ A ∪ B := by
    intro p hp
    obtain ⟨_, ⟨q, hq, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp (hS hp) _ hr
    by_cases h : reach q
    · exact Or.inl (mem_iUnion.2 ⟨⟨q, hq, h⟩, hdist⟩)
    · exact Or.inr (mem_iUnion.2 ⟨⟨q, hq, h⟩, hdist⟩)
  have hA : (S ∩ A).Nonempty :=
    ⟨embed x, ha, mem_iUnion.2 ⟨⟨x, hx, .refl⟩, Metric.mem_ball_self hr⟩⟩
  have hB : (S ∩ B).Nonempty :=
    ⟨embed y, hb, mem_iUnion.2 ⟨⟨y, hy, hn⟩, Metric.mem_ball_self hr⟩⟩
  obtain ⟨p, _, hpA, hpB⟩ := hconn A B (isOpen_iUnion fun _ => Metric.isOpen_ball)
    (isOpen_iUnion fun _ => Metric.isOpen_ball) hcover hA hB
  obtain ⟨q, hq⟩ := mem_iUnion.1 hpA
  obtain ⟨r, hr'⟩ := mem_iUnion.1 hpB
  have hdist : dist (embed q.1) (embed r.1) < (ε : ℝ) := by
    have H := dist_triangle (embed q.1) p (embed r.1)
    have Hq := Metric.mem_ball.mp hq
    have Hr := Metric.mem_ball.mp hr'
    rw [dist_comm] at Hq
    linarith
  apply r.2.2
  apply q.2.2.tail
  refine ⟨q.2.1, r.2.1, fun i => ?_⟩
  have h := (dist_pi_lt_iff hεR).1 hdist i
  rw [Real.dist_eq] at h
  change |(q.1 i : ℝ) - (r.1 i : ℝ)| < (ε : ℝ) at h
  exact_mod_cast h

theorem fineConnected_of_segment {tests : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℚ}
    (hx : Legal tests budgets x) (hy : Legal tests budgets y) {f : ℝ → I → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (h0 : f 0 = embed x) (h1 : f 1 = embed y)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ closure (embed '' {q | Legal tests budgets q})) :
    FineConnected tests budgets x y :=
  fineConnected_of_preconnected hx hy (isPreconnected_Icc.image f hf)
    ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
    (by rintro _ ⟨t, ht, rfl⟩; exact hclose t ht)

end MovingProjection
