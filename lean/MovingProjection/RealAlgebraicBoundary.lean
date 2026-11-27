import MovingProjection.AlgebraicBoundary
import MovingProjection.RealComponents
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.Path

/-! The same algebraic reductions for real path-component membership. -/

namespace MovingProjection

open Set ConstraintLogic
open scoped BigOperators

namespace MonotoneCircuitMarkov.Circuit

variable {n : ℕ} (C : Circuit n)

theorem algebraic_real_path_iff_value :
    JoinedIn {x | RealLegal C.algebraicTests C.algebraicBudgets x}
      (embed (spectrum (n := n) false)) (embed (spectrum (n := n) true)) ↔
        C.value C.out = true :=
  (fineConnected_iff_real_joinedIn (C.algebraic_endpoint_legal false)
    (C.algebraic_endpoint_legal true) C.algebraic_bounded).symm.trans C.algebraic_fine_iff_value

end MonotoneCircuitMarkov.Circuit

namespace AlgebraicConstraintLogic

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
variable (G : Graph E V)

def RealLawful (x : Index E V → ℝ) : Prop :=
  RealLegal (tests G) (guards G) x ∧ ∀ i : E, x (.inl (i,false)) + x (.inl (i,true)) = 1

theorem realLawful_embed {x : Index E V → ℚ} (hx : Lawful G x) : RealLawful G (embed x) := by
  refine ⟨realLegal_embed hx.1, fun i => ?_⟩
  change (x (.inl (i,false)) : ℝ) + (x (.inl (i,true)) : ℝ) = 1
  exact_mod_cast hx.2 i

private theorem isClosed_realLawful : IsClosed {x | RealLawful G x} := by
  unfold RealLawful
  simp only [setOf_and, setOf_forall]
  exact (isClosed_realLegal _ _).inter (isClosed_iInter fun i => isClosed_eq (by fun_prop)
    continuous_const)

private theorem realMonomial_single (x : Index E V → ℝ) (j : Index E V) :
    realMonomial (fun l => if l = j then 1 else 0) x = x j := by
  unfold realMonomial
  rw [Finset.prod_congr rfl (g := fun l => if l = j then x l else 1)]
  · simp
  · intro l _
    by_cases h : l = j <;> simp [h]

private theorem real_charge {x : Index E V → ℝ} (hx : RealLawful G x)
    (i : E) (b : Bool) (hb : x (.inl (i,b)) ≠ 0) :
    x (.inr (G.tail i b,i)) = (G.weight i : ℝ) := by
  let j : Index E V := .inl (i,b)
  let k : Index E V := .inr (G.tail i b,i)
  have h := hx.1.1 (activationTest G i b) (List.mem_map.mpr ⟨(i,b), by simp, rfl⟩)
  change realMonomial (fun l => (if l = j then 1 else 0) + (if l = k then 1 else 0)) x =
    (G.weight i : ℝ) * realMonomial (fun l => if l = j then 1 else 0) x at h
  have hprod :
      realMonomial (fun l => (if l = j then 1 else 0) + (if l = k then 1 else 0)) x =
        x j * x k := by
    simp only [realMonomial, pow_add, Finset.prod_mul_distrib]
    exact congrArg₂ (· * ·) (realMonomial_single x j) (realMonomial_single x k)
  rw [hprod, realMonomial_single, mul_comm (G.weight i : ℝ)] at h
  exact mul_left_cancel₀ hb h

private theorem real_capacity {x : Index E V → ℝ} (hx : RealLawful G x) (v : V) :
    ∑ i : E, |x (.inr (v,i))| ≤ (G.capacity v : ℝ) := by
  have h := hx.1.2 (chargeBudget G v) (List.mem_append_left _
    (List.mem_map.mpr ⟨v, by simp, rfl⟩))
  simpa [chargeBudget] using h

def realRepresents (x : Index E V → ℝ) (a : E → Bool) : Prop := ∀ i, x (.inl (i, a i)) ≠ 0

private theorem legal_of_realRepresents {x : Index E V → ℝ} (hx : RealLawful G x)
    {a : E → Bool} (ha : realRepresents x a) : G.Legal a := by
  intro v
  have h : (∑ i, if G.tail i (a i) = v then (G.weight i : ℝ) else 0) ≤ (G.capacity v : ℝ) := by
    apply le_trans _ (real_capacity G hx v)
    apply Finset.sum_le_sum
    intro i _
    split_ifs with he
    · rw [← he, real_charge G hx i (a i) (ha i), abs_of_pos]
      exact_mod_cast G.weight_pos i
    · exact abs_nonneg _
  apply (Rat.cast_le (K := ℝ)).mp
  unfold Graph.Load
  rw [Rat.cast_sum]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

private theorem flips_of_realRepresents {x : Index E V → ℝ} (hx : RealLawful G x)
    {a b : E → Bool} (ha : realRepresents x a) (hb : realRepresents x b) : G.Flips a b :=
  G.flips_of_legal_mixes fun _ hc =>
    legal_of_realRepresents G hx fun i => (hc i).elim (fun h => h ▸ ha i) (fun h => h ▸ hb i)

private theorem real_common {x y : Index E V → ℝ} (hx : RealLawful G x) (hy : RealLawful G y)
    (h : dist x y < 1) : ∃ a, realRepresents x a ∧ realRepresents y a := by
  exact Graph.common_nonzero_choices (p := fun i b => x (.inl (i,b)))
    (q := fun i b => y (.inl (i,b))) zero_lt_one hx.2 hy.2 (fun i => by
      simpa [Real.dist_eq] using (dist_pi_lt_iff zero_lt_one).mp h (.inl (i,false)))

omit [Fintype E] [DecidableEq E] [Fintype V] in
private theorem realRepresents_endpoint (a b : E → Bool) :
    realRepresents (embed (endpoint G a)) b ↔ a = b := by
  change (∀ i, ((G.corner 1 a).toggle i (b i) : ℝ) ≠ 0) ↔ _
  simpa only [Rat.cast_ne_zero] using G.represents_corner
    (show (0 : ℚ) < 1 by norm_num) a b

/-- Sampling a real path finely enough shares one orientation at each adjacent pair. -/
theorem flips_of_real_path {a b : E → Bool}
    (h : JoinedIn {x | RealLawful G x} (embed (endpoint G a)) (embed (endpoint G b))) :
    G.Flips a b := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨δ, hδ, hnear⟩ := Metric.uniformContinuous_iff.mp p.uniformContinuous 1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn₀ : (0 : ℝ) < n := (div_pos one_pos hδ).trans hn
  have hm : 1 / (n : ℝ) < δ := (div_lt_iff₀ hn₀).mpr
    (by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn)
  let sample (j : ℕ) (hj : j ≤ n) : unitInterval :=
    ⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg j) hn₀.le,
      (div_le_one hn₀).mpr (by exact_mod_cast hj)⟩
  have hzero : sample 0 (Nat.zero_le n) = 0 := by ext; simp [sample]
  have hone : sample n le_rfl = 1 := by ext; simp [sample, hn₀.ne']
  have hstep (j : ℕ) (hj : j + 1 ≤ n) :
      dist (sample j (Nat.le_of_succ_le hj)) (sample (j+1) hj) < δ := by
    change dist ((j : ℝ) / n) ((↑(j+1) : ℝ) / n) < δ
    rw [Real.dist_eq, ← sub_div, Nat.cast_add, Nat.cast_one,
      show (j : ℝ) - (j + 1) = -1 by ring, neg_div, abs_neg,
      abs_of_nonneg (div_nonneg zero_le_one hn₀.le)]
    exact hm
  have hind (j : ℕ) (hj : j ≤ n) (o : E → Bool)
      (ho : realRepresents (p (sample j hj)) o) : G.Flips a o := by
    induction j generalizing o with
    | zero =>
      rw [hzero, p.source] at ho
      rw [(realRepresents_endpoint G a o).mp ho]
    | succ j ih =>
      let hj' := Nat.le_of_succ_le hj
      have hpre : RealLawful G (p (sample j hj')) := hp _
      have hpost : RealLawful G (p (sample (j+1) hj)) := hp _
      obtain ⟨r, hleft, hright⟩ := real_common G hpre hpost (hnear (hstep j hj))
      exact (ih hj' r hleft).trans (flips_of_realRepresents G hpost hright ho)
  apply hind n le_rfl
  rw [hone, p.target]
  exact (realRepresents_endpoint G b b).mpr rfl

private theorem real_segment {a b : Index E V → ℚ}
    (h : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → Lawful G (fun i => Graph.mix (a i) (b i) t)) :
    JoinedIn {x | RealLawful G x} (embed a) (embed b) := by
  let f (t : ℝ) (i : Index E V) := (1 - t) * embed a i + t * embed b i
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hclosed : IsClosed (f ⁻¹' {x | RealLawful G x}) := (isClosed_realLawful G).preimage hf
  have hdense : Icc (0 : ℝ) 1 ⊆ closure (((↑) : ℚ → ℝ) '' Icc 0 1) := by
    have he := closure_ordConnected_inter_rat (ordConnected_Icc (a := (0 : ℝ)) (b := 1))
      (show (Icc (0 : ℝ) 1).Nontrivial from ⟨0, ⟨le_rfl, zero_le_one⟩,
        1, ⟨zero_le_one, le_rfl⟩, zero_ne_one⟩)
    have he' : ((↑) : ℚ → ℝ) '' Icc 0 1 = Icc (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩, mem_range_self t⟩
      · rintro ⟨hy, ⟨t, rfl⟩⟩
        exact ⟨t, ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩, rfl⟩
    rw [he', he, isClosed_Icc.closure_eq]
  have hsub : (((↑) : ℚ → ℝ) '' Icc 0 1) ⊆ f ⁻¹' {x | RealLawful G x} := by
    rintro _ ⟨t, ht, rfl⟩
    have he : f (t : ℝ) = embed (fun i => Graph.mix (a i) (b i) t) := by
      funext i
      simp [f, embed, Graph.mix]
    change RealLawful G (f (t : ℝ))
    rw [he]
    exact realLawful_embed G (h t ht.1 ht.2)
  apply JoinedIn.ofLine hf.continuousOn (by funext i; simp [f]) (by funext i; simp [f])
  rintro _ ⟨t, ht, rfl⟩
  exact closure_minimal hsub hclosed (hdense ht)

private theorem flip_real_path {a b : E → Bool} (h : G.Flip a b) :
    JoinedIn {x | RealLawful G x} (embed (endpoint G a)) (embed (endpoint G b)) := by
  obtain ⟨h₁, h₂, h₃⟩ := G.flip_segments_lawful (k := 1) h
  have hpiece {p q : Graph.Point E V}
      (hp : ∀ i b, 0 ≤ p.toggle i b ∧ p.toggle i b ≤ 1)
      (hq : ∀ i b, 0 ≤ q.toggle i b ∧ q.toggle i b ≤ 1)
      (hl : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → Graph.Lawful G 1 (Graph.segment p q t)) :
      JoinedIn {x | RealLawful G x} (embed (pack p)) (embed (pack q)) := by
    apply real_segment G
    intro t ht ht'
    have he : (fun i => Graph.mix (pack p i) (pack q i) t) = pack (Graph.segment p q t) := by
      funext i
      cases i <;> rfl
    rw [he]
    apply (lawful_iff G _).mpr
    rw [read_pack]
    refine ⟨hl t ht ht', fun i b => ?_⟩
    change |Graph.mix (p.toggle i b) (q.toggle i b) t| ≤ 1
    rw [abs_of_nonneg (Graph.mix_nonneg (hp i b).1 (hq i b).1 ht ht')]
    exact Graph.mix_le (hp i b).2 (hq i b).2 ht ht'
  have hc (o : E → Bool) (i : E) (s : Bool) :
      0 ≤ (G.corner 1 o).toggle i s ∧ (G.corner 1 o).toggle i s ≤ 1 := by
    by_cases ho : o i = s <;> norm_num [Graph.corner, ho]
  have hpa : ∀ i s, 0 ≤ (G.preload 1 a b).toggle i s ∧ (G.preload 1 a b).toggle i s ≤ 1 := hc a
  have hpb : ∀ i s, 0 ≤ (G.preload 1 b a).toggle i s ∧ (G.preload 1 b a).toggle i s ≤ 1 := hc b
  exact (hpiece (hc a) hpa h₁).trans ((hpiece hpa hpb h₂).trans (hpiece hpb (hc b) h₃))

theorem real_path_iff_flips {a b : E → Bool} (ha : G.Legal a) :
    JoinedIn {x | RealLawful G x} (embed (endpoint G a)) (embed (endpoint G b)) ↔ G.Flips a b := by
  refine ⟨flips_of_real_path G, fun h => ?_⟩
  induction h with
  | refl => exact JoinedIn.refl (realLawful_embed G (endpoint_lawful G ha))
  | tail _ hf ih => exact ih.trans (flip_real_path G hf)

theorem network_real_path_iff_flips (N : Network E V) {a b : E → Bool} (ha : N.Legal a) :
    JoinedIn {x | RealLawful N.scaled x}
      (embed (endpoint N.scaled a)) (embed (endpoint N.scaled b)) ↔ N.Flips a b :=
  (real_path_iff_flips N.scaled ((N.legal_iff_scaled a).mp ha)).trans (N.flips_iff_scaled a b).symm

end AlgebraicConstraintLogic
end MovingProjection
