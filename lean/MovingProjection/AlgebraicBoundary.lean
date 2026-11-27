import MovingProjection.MonotoneCircuitMarkov
import MovingProjection.ConstraintLogic

/-! The endpoint reductions for the algebraic boundary. The Turing-machine
resource bounds are in BoundaryCorollaries.md. -/

namespace MovingProjection

namespace MonotoneCircuitMarkov.Circuit

variable {n : ℕ} (C : Circuit n)

noncomputable abbrev algebraicTests := (C.D.fiber (profile (n := n))).spectralChecks
noncomputable abbrev algebraicBudgets := spectrumBudgets (M := Mark n) (I := Unit) C.D.κ

theorem algebraic_endpoint_legal (b : Bool) :
    Legal C.algebraicTests C.algebraicBudgets (spectrum (n := n) b) :=
  (C.endpoint b).legal.2.2.2.1

theorem algebraic_bounded :
    ∃ B : ℝ, ∀ a, Legal C.algebraicTests C.algebraicBudgets a → ‖embed a‖ ≤ B :=
  bounded_of_budget_cover (spectrumBudgets_covers C.D.κ)

theorem algebraic_fine_iff_value :
    FineConnected C.algebraicTests C.algebraicBudgets
      (spectrum (n := n) false) (spectrum (n := n) true) ↔ C.value C.out = true := by
  rw [fineConnected_iff_signedCore (C.algebraic_endpoint_legal false)
    (C.algebraic_endpoint_legal true) C.algebraic_bounded, ← C.native_fine_iff_value,
    C.instrument.exact_six_iff]
  change _ ↔ (profile (n := n) ≤ profile ∧
    C.D.signature profile (C.endpoint false).law = C.D.signature profile (C.endpoint true).law)
  simp only [le_rfl, true_and, Protocol.signature]
  rfl

end MonotoneCircuitMarkov.Circuit

namespace AlgebraicConstraintLogic

open ConstraintLogic
open scoped BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

abbrev Index (E V : Type*) := (E × Bool) ⊕ (V × E)

def pack (p : Graph.Point E V) : Index E V → ℚ
  | .inl (i,b) => p.toggle i b
  | .inr (v,i) => p.charge v i

def read (x : Index E V → ℚ) : Graph.Point E V :=
  ⟨fun i b => x (.inl (i,b)), fun v i => x (.inr (v,i))⟩

omit [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V] in
@[simp] theorem read_pack (p : Graph.Point E V) : read (pack p) = p := rfl

omit [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V] in
@[simp] theorem pack_read (x : Index E V → ℚ) : pack (read x) = x := by
  funext i
  cases i <;> rfl

variable (G : Graph E V)

def activationTest (i : E) (b : Bool) : MonomialTest (Index E V) :=
  let j : Index E V := .inl (i,b)
  let k : Index E V := .inr (G.tail i b,i)
  ⟨⟨fun l => (if l = j then 1 else 0) + (if l = k then 1 else 0),
     fun l => if l = j then 1 else 0⟩, G.weight i⟩

private theorem monomial_single (x : Index E V → ℚ) (j : Index E V) :
    monomial (fun l => if l = j then 1 else 0) x = x j := by
  unfold monomial
  rw [Finset.prod_congr rfl (g := fun l => if l = j then x l else 1)]
  · simp
  · intro l _
    by_cases h : l = j <;> simp [h]

theorem activationTest_iff (x : Index E V → ℚ) (i : E) (b : Bool) :
    (activationTest G i b).holds x ↔
      (read x).toggle i b ≠ 0 → (read x).charge (G.tail i b) i = G.weight i := by
  let j : Index E V := .inl (i,b)
  let k : Index E V := .inr (G.tail i b,i)
  have hprod : monomial (fun l => (if l = j then 1 else 0) + (if l = k then 1 else 0)) x =
      x j * x k := by
    simp only [monomial, pow_add, Finset.prod_mul_distrib]
    exact congrArg₂ (· * ·) (monomial_single x j) (monomial_single x k)
  change (monomial (fun l => (if l = j then 1 else 0) + (if l = k then 1 else 0)) x =
    G.weight i * monomial (fun l => if l = j then 1 else 0) x) ↔ _
  rw [hprod, monomial_single, mul_comm (G.weight i)]
  change (x j * x k = x j * G.weight i) ↔ _
  constructor
  · exact fun h hn => mul_left_cancel₀ hn h
  · intro h
    by_cases hn : x j = 0
    · simp [hn]
    · exact congrArg (x j * ·) (h hn)

def chargeBudget (v : V) : MarkBudget (Index E V) :=
  ⟨Finset.univ.map ⟨fun i => .inr (v,i), fun _ _ h => (Sum.inr.inj h |> congrArg Prod.snd)⟩,
    G.capacity v⟩

def toggleBudget (i : E) (b : Bool) : MarkBudget (Index E V) := ⟨{.inl (i,b)}, 1⟩

noncomputable def tests : List (MonomialTest (Index E V)) :=
  Finset.univ.toList.map fun ib : E × Bool => activationTest G ib.1 ib.2

noncomputable def guards : List (MarkBudget (Index E V)) :=
  (Finset.univ.toList.map (chargeBudget G)) ++
    (Finset.univ.toList.map fun ib : E × Bool => toggleBudget (V := V) ib.1 ib.2)

/-- The added rows are exactly one affine trinomial per edge. -/
def Lawful (x : Index E V → ℚ) : Prop :=
  Legal (tests G) (guards G) x ∧ ∀ i : E, x (.inl (i,false)) + x (.inl (i,true)) = 1

theorem lawful_iff (x : Index E V → ℚ) :
    Lawful G x ↔ Graph.Lawful G 1 (read x) ∧ ∀ i b, |(read x).toggle i b| ≤ 1 := by
  have hcap (v : V) : (∑ j ∈ (chargeBudget G v).indices, |x j|) =
      ∑ i, |(read x).charge v i| := by
    unfold chargeBudget read
    exact Finset.sum_map _ _ _
  constructor
  · rintro ⟨⟨ht, hg⟩, hsum⟩
    refine ⟨⟨hsum, fun i b => (activationTest_iff G x i b).mp (ht _ ?_),
      fun v => ?_⟩, fun i b => ?_⟩
    · exact List.mem_map.mpr ⟨(i,b), by simp, rfl⟩
    · rw [← hcap]
      exact hg _ (List.mem_append_left _ (List.mem_map.mpr ⟨v, by simp, rfl⟩))
    · simpa [toggleBudget] using hg _ (List.mem_append_right _
        (List.mem_map.mpr ⟨(i,b), by simp, rfl⟩))
  · rintro ⟨⟨hs, ht, hg⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, hs⟩
    · intro r hr
      obtain ⟨⟨i,b⟩, _, rfl⟩ := List.mem_map.mp hr
      exact (activationTest_iff G x i b).mpr (ht i b)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
        rw [hcap]
        exact hg v
      · obtain ⟨⟨i,b⟩, _, rfl⟩ := List.mem_map.mp hr
        simpa [toggleBudget] using hb i b

theorem bounded :
    ∃ B : ℝ, ∀ x, Lawful G x → ‖embed x‖ ≤ B := by
  obtain ⟨B, hB⟩ := bounded_of_budget_cover (tests := (tests G)) (budgets := (guards G))
    (hcover := fun j => by
      rcases j with ⟨i,b⟩ | ⟨v,i⟩
      · refine ⟨toggleBudget i b, List.mem_append_right _
          (List.mem_map.mpr ⟨(i,b), by simp, rfl⟩), by simp [toggleBudget]⟩
      · refine ⟨chargeBudget G v, List.mem_append_left _
          (List.mem_map.mpr ⟨v, by simp, rfl⟩), ?_⟩
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  exact ⟨B, fun x hx => hB x hx.1⟩

def Step (ε : ℚ) (x y : Index E V → ℚ) : Prop :=
  Lawful G x ∧ Lawful G y ∧ ∀ i, |x i - y i| < ε

abbrev Chain (ε : ℚ) := Relation.ReflTransGen (Step G ε)

def endpoint (a : E → Bool) : Index E V → ℚ := pack (G.corner 1 a)

theorem endpoint_lawful {a : E → Bool} (ha : G.Legal a) : Lawful G (endpoint G a) := by
  apply (lawful_iff G _).mpr
  rw [endpoint, read_pack]
  refine ⟨G.corner_lawful ha, fun i b => ?_⟩
  by_cases h : a i = b <;> simp [Graph.corner, h]

private def clip (x : ℚ) := min 1 (max x 0)

private theorem clip_sum {x y : ℚ} (h : x + y = 1) : clip x + clip y = 1 := by
  by_cases hx : x ≤ 0
  · simp [clip, max_eq_right hx, max_eq_left (show 0 ≤ y by linarith),
      min_eq_left (show 1 ≤ y by linarith)]
  · by_cases hx' : 1 ≤ x
    · simp [clip, max_eq_left (show 0 ≤ x by linarith), min_eq_left hx',
        max_eq_right (show y ≤ 0 by linarith)]
    · have hy : 0 ≤ y := by linarith
      have hy' : y ≤ 1 := by linarith
      simpa [clip, max_eq_left (show 0 ≤ x by linarith), max_eq_left hy,
        min_eq_right (show x ≤ 1 by linarith), min_eq_right hy'] using h

private theorem clip_dist (x y : ℚ) : |clip x - clip y| ≤ |x - y| := by
  unfold clip
  have h := abs_min_sub_min_le_max (1 : ℚ) (max x 0) 1 (max y 0)
  exact (by simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (max x 0 - max y 0))] using h :
    |min 1 (max x 0) - min 1 (max y 0)| ≤ |max x 0 - max y 0|).trans
    (abs_max_sub_max_le_abs x y 0)

private def clipped (p : Graph.Point E V) : Graph.Point E V :=
  ⟨fun i b => clip (p.toggle i b), p.charge⟩

private theorem clipped_lawful {p : Graph.Point E V} (hp : Graph.Lawful G 1 p) :
    Lawful G (pack (clipped p)) := by
  apply (lawful_iff G _).mpr
  rw [read_pack]
  refine ⟨⟨fun i => clip_sum (hp.1 i), fun i b h => ?_, hp.2.2⟩, fun i b => ?_⟩
  · exact hp.2.1 i b (fun hz => h (by simp [clipped, clip, hz]))
  · change |clip _| ≤ 1
    rw [abs_of_nonneg (le_min zero_le_one (le_max_right _ _))]
    exact min_le_left _ _

omit [Fintype E] [DecidableEq E] [Fintype V] in
private theorem clipped_corner (a : E → Bool) : clipped (G.corner 1 a) = G.corner 1 a := by
  ext
  · rename_i i b
    by_cases h : a i = b <;> norm_num [clipped, clip, Graph.corner, h]
  · rfl

theorem chain_of_flips {a b : E → Bool} (h : G.Flips a b) {ε : ℚ} (hε : 0 < ε) :
    Chain G ε (endpoint G a) (endpoint G b) := by
  have hc := G.chain_of_flips (k := 1) h hε
  have hf (p q : Graph.Point E V) (hpq : Graph.Step G 1 ε p q) :
      Step G ε (pack (clipped p)) (pack (clipped q)) := by
    refine ⟨clipped_lawful G hpq.1, clipped_lawful G hpq.2.1, ?_⟩
    rintro (⟨i,b⟩ | ⟨v,i⟩)
    · exact (clip_dist _ _).trans_lt (hpq.2.2.1 i b)
    · exact hpq.2.2.2 v i
  have hm := Relation.ReflTransGen.lift (pack ∘ clipped) hf hc
  change Chain G ε (pack (clipped (G.corner 1 a))) (pack (clipped (G.corner 1 b))) at hm
  simpa only [endpoint, clipped_corner] using hm

theorem flips_of_chain {a b : E → Bool} (ha : G.Legal a)
    (h : Chain G 1 (endpoint G a) (endpoint G b)) : G.Flips a b := by
  have hf (x y : Index E V → ℚ) (hxy : Step G 1 x y) :
      Graph.Step G 1 1 (read x) (read y) :=
    ⟨((lawful_iff G x).mp hxy.1).1, ((lawful_iff G y).mp hxy.2.1).1,
      fun i b => hxy.2.2 (.inl (i,b)), fun v i => hxy.2.2 (.inr (v,i))⟩
  have hc := Relation.ReflTransGen.lift read hf h
  simp only [endpoint, read_pack] at hc
  exact G.flips_of_chain zero_lt_one (G.corner_lawful ha)
    ((G.represents_corner zero_lt_one a a).mpr rfl) ((G.represents_corner zero_lt_one b b).mpr rfl) hc

theorem fine_iff_flips {a b : E → Bool} (ha : G.Legal a) :
    (∀ ε : ℚ, 0 < ε → Chain G ε (endpoint G a) (endpoint G b)) ↔ G.Flips a b :=
  ⟨fun h => flips_of_chain G ha (h 1 zero_lt_one), fun h _ hε => chain_of_flips G h hε⟩

end AlgebraicConstraintLogic
end MovingProjection
