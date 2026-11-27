import MovingProjection.ClauseReconfiguration
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A rational realization of constraint-logic reconfiguration. Choosing an
end of an edge requires its entire charge, even during an interpolation. -/

namespace MovingProjection.ConstraintLogic

open scoped BigOperators

variable {E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]

structure Graph (E V : Type*) where
  tail : E → Bool → V
  weight : E → ℚ
  capacity : V → ℚ
  weight_pos : ∀ i, 0 < weight i

namespace Graph

variable (G : Graph E V)

def Load (a : E → Bool) (v : V) : ℚ :=
  ∑ i, if G.tail i (a i) = v then G.weight i else 0

def Legal (a : E → Bool) : Prop := ∀ v, G.Load a v ≤ G.capacity v

def Flip (a b : E → Bool) : Prop :=
  G.Legal a ∧ G.Legal b ∧ ∃ i, ∀ j ≠ i, a j = b j

abbrev Flips := Relation.ReflTransGen G.Flip

@[ext] structure Point (E V : Type*) where
  toggle : E → Bool → ℚ
  charge : V → E → ℚ

variable {k : ℚ}

def Lawful (k : ℚ) (p : Point E V) : Prop :=
  (∀ i, p.toggle i false + p.toggle i true = k) ∧
  (∀ i b, p.toggle i b ≠ 0 → p.charge (G.tail i b) i = G.weight i) ∧
  (∀ v, ∑ i, |p.charge v i| ≤ G.capacity v)

def Represents (p : Point E V) (a : E → Bool) : Prop := ∀ i, p.toggle i (a i) ≠ 0

def Near (ε : ℚ) (p q : Point E V) : Prop :=
  (∀ i b, |p.toggle i b - q.toggle i b| < ε) ∧
  (∀ v i, |p.charge v i - q.charge v i| < ε)

def Step (k ε : ℚ) (p q : Point E V) : Prop :=
  G.Lawful k p ∧ G.Lawful k q ∧ Near ε p q

abbrev Chain (k ε : ℚ) := Relation.ReflTransGen (G.Step k ε)

omit [DecidableEq E] in
theorem legal_of_represents {p : Point E V} {a : E → Bool}
    (hp : G.Lawful k p) (ha : Represents p a) : G.Legal a := by
  intro v
  apply le_trans _ (hp.2.2 v)
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · rw [← h, hp.2.1 i (a i) (ha i), abs_of_pos (G.weight_pos i)]
  · exact abs_nonneg _

/-- All combinations of the endpoint choices can be traversed by single-edge flips. -/
theorem flips_of_legal_mixes {a b : E → Bool}
    (hlegal : ∀ c, (∀ i, c i = a i ∨ c i = b i) → G.Legal c) : G.Flips a b := by
  let mix (s : Finset E) (i : E) := if i ∈ s then b i else a i
  have hm (s : Finset E) : G.Legal (mix s) := by
    apply hlegal
    intro i
    by_cases hi : i ∈ s <;> simp [mix, hi]
  have h (s : Finset E) : G.Flips a (mix s) := by
    induction s using Finset.induction_on with
    | empty => simpa [mix] using (Relation.ReflTransGen.refl : G.Flips a a)
    | @insert i s _ ih =>
      apply ih.tail
      refine ⟨hm s, hm (insert i s), i, ?_⟩
      intro j hj
      simp [mix, hj]
  simpa [mix] using h Finset.univ

theorem flips_of_represents {p : Point E V} {a b : E → Bool}
    (hp : G.Lawful k p) (ha : Represents p a) (hb : Represents p b) : G.Flips a b :=
  G.flips_of_legal_mixes fun _ hc =>
    G.legal_of_represents hp fun i => (hc i).elim (fun h => h ▸ ha i) (fun h => h ▸ hb i)

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
theorem common_nonzero_choices {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p q : E → Bool → K} {k : K} (hk : 0 < k)
    (hp : ∀ i, p i false + p i true = k) (hq : ∀ i, q i false + q i true = k)
    (h : ∀ i, |p i false - q i false| < k) :
    ∃ a : E → Bool, (∀ i, p i (a i) ≠ 0) ∧ (∀ i, q i (a i) ≠ 0) := by
  classical
  let a (i : E) : Bool := if p i false ≠ 0 ∧ q i false ≠ 0 then false else true
  have ht (i : E) (hi : ¬(p i false ≠ 0 ∧ q i false ≠ 0)) :
      p i true ≠ 0 ∧ q i true ≠ 0 := by
    push_neg at hi
    have hsum := hp i
    have hsum' := hq i
    have hd := abs_lt.mp (h i)
    constructor <;> intro he
    · have hn : p i false ≠ 0 := by linarith
      have hz := hi hn
      linarith [hd.2]
    · have hz : p i false = 0 := by
        by_contra hn
        have := hi hn
        linarith
      linarith [hd.1]
  refine ⟨a, fun i => ?_, fun i => ?_⟩ <;>
    by_cases hi : p i false ≠ 0 ∧ q i false ≠ 0
  · simpa only [a, if_pos hi] using hi.1
  · simpa only [a, if_neg hi] using (ht i hi).1
  · simpa only [a, if_pos hi] using hi.2
  · simpa only [a, if_neg hi] using (ht i hi).2

omit [DecidableEq E] [DecidableEq V] in
theorem common_orientation {p q : Point E V} (hk : 0 < k)
    (hp : G.Lawful k p) (hq : G.Lawful k q)
    (h : ∀ i, |p.toggle i false - q.toggle i false| < k) :
    ∃ a, Represents p a ∧ Represents q a :=
  common_nonzero_choices hk hp.1 hq.1 h

theorem flips_of_chain {p q : Point E V} {a b : E → Bool} (hk : 0 < k)
    (hp : G.Lawful k p) (ha : Represents p a) (hb : Represents q b)
    (h : G.Chain k k p q) : G.Flips a b := by
  revert b
  induction h with
  | refl => exact fun hb => G.flips_of_represents hp ha hb
  | @tail u v _ hedge ih =>
    intro b hb
    obtain ⟨c, hu, hv⟩ := G.common_orientation hk hedge.1 hedge.2.1 (fun i => hedge.2.2.1 i false)
    exact (ih hu).trans (G.flips_of_represents hedge.2.1 hv hb)

def corner (k : ℚ) (a : E → Bool) : Point E V where
  toggle i b := if a i = b then k else 0
  charge v i := if G.tail i (a i) = v then G.weight i else 0

omit [Fintype E] [DecidableEq E] in
theorem represents_corner (hk : 0 < k) (a b : E → Bool) :
    Represents (G.corner k a) b ↔ a = b := by
  constructor
  · intro h
    funext i
    simpa [corner, hk.ne'] using h i
  · rintro rfl i
    simp [corner, hk.ne']

omit [DecidableEq E] [Fintype E] in
theorem toggle_sum_corner (a : E → Bool) (i : E) :
    (G.corner k a).toggle i false + (G.corner k a).toggle i true = k := by
  cases h : a i <;> simp [corner, h]

omit [DecidableEq E] in
theorem corner_lawful {a : E → Bool} (ha : G.Legal a) : G.Lawful k (G.corner k a) := by
  refine ⟨G.toggle_sum_corner a, ?_, ?_⟩
  · intro i b hb
    have he : a i = b := by
      by_contra he
      exact hb (by simp [corner, he])
    simp [corner, he]
  · intro v
    have h (i : E) : 0 ≤ (G.corner k a).charge v i := by
      simp [corner, apply_ite, (G.weight_pos i).le]
    simp only [abs_of_nonneg (h _)]
    exact ha v

def mix (r s t : ℚ) : ℚ := (1 - t) * r + t * s

theorem mix_self (r t : ℚ) : mix r r t = r := by unfold mix; ring

theorem mix_nonneg {r s t : ℚ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    0 ≤ mix r s t := add_nonneg (mul_nonneg (sub_nonneg.mpr ht') hr) (mul_nonneg ht hs)

theorem mix_le {r s t B : ℚ} (hr : r ≤ B) (hs : s ≤ B) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    mix r s t ≤ B := by
  rw [← mix_self B t]
  exact add_le_add (mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr ht'))
    (mul_le_mul_of_nonneg_left hs ht)

theorem mix_dist (r s p q : ℚ) : |mix r s p - mix r s q| = |s - r| * |p - q| := by
  rw [show mix r s p - mix r s q = (s - r) * (p - q) by unfold mix; ring, abs_mul]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
def segment (p q : Point E V) (t : ℚ) : Point E V :=
  ⟨fun i b => mix (p.toggle i b) (q.toggle i b) t,
    fun v i => mix (p.charge v i) (q.charge v i) t⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
@[simp] theorem segment_zero (p q : Point E V) : segment p q 0 = p := by
  cases p
  simp [segment, mix]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
@[simp] theorem segment_one (p q : Point E V) : segment p q 1 = q := by
  cases q
  simp [segment, mix]

/-- A finite coordinatewise affine path with bounded coordinate slopes has
rational meshes. The target state type may carry an arbitrary legality proof. -/
theorem mesh_of_lipschitz {T : Type*} {step : ℚ → T → T → Prop}
    (s : (t : ℚ) → 0 ≤ t → t ≤ 1 → T) {B ε : ℚ}
    (hB : 0 < B) (hε : 0 < ε)
    (h : ∀ p q hp hp' hq hq', B * |p - q| < ε →
      step ε (s p hp hp') (s q hq hq')) :
    Relation.ReflTransGen (step ε) (s 0 le_rfl zero_le_one) (s 1 zero_le_one le_rfl) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ε)
  have hn₀ := (div_pos hB hε).trans hn
  have hsmall : B / (n : ℚ) < ε :=
    (div_lt_iff₀ hn₀).mpr (by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn)
  let sample (j : ℕ) (hj : j ≤ n) : T :=
    s ((j : ℚ) / n) (div_nonneg (Nat.cast_nonneg j) hn₀.le)
      ((div_le_one hn₀).2 (by exact_mod_cast hj))
  have hs (j : ℕ) (hj : j ≤ n) :
      Relation.ReflTransGen (step ε) (sample 0 (Nat.zero_le n)) (sample j hj) := by
    induction j with
    | zero => exact .refl
    | succ j ih =>
      apply (ih ((Nat.le_succ _).trans hj)).tail
      apply h
      rw [Nat.cast_succ, ← sub_div, show (j : ℚ) - (j + 1) = -1 by ring,
        neg_div, abs_neg, abs_of_nonneg (by positivity), mul_one_div]
      exact hsmall
  simpa [sample, hn₀.ne'] using hs n le_rfl

variable [Fintype V]

omit [DecidableEq E] [DecidableEq V] in
private theorem segment_mesh {p q : Point E V}
    (h : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → G.Lawful k (segment p q t))
    {ε : ℚ} (hε : 0 < ε) : G.Chain k ε p q := by
  let T := ∑ i, ∑ b, |q.toggle i b - p.toggle i b|
  let C := ∑ v, ∑ i, |q.charge v i - p.charge v i|
  let B := 1 + T + C
  have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hB : 0 < B := by dsimp only [B]; linarith
  have hb₁ (i : E) (b : Bool) : |q.toggle i b - p.toggle i b| ≤ B := by
    have h1 := Finset.single_le_sum
      (s := (Finset.univ : Finset Bool)) (f := fun j => |q.toggle i j - p.toggle i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : (∑ b, |q.toggle i b - p.toggle i b|) ≤ T := Finset.single_le_sum
      (s := (Finset.univ : Finset E))
      (f := fun j => ∑ b, |q.toggle j b - p.toggle j b|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
    exact (h1.trans h2).trans (by dsimp only [B]; linarith)
  have hb₂ (v : V) (i : E) : |q.charge v i - p.charge v i| ≤ B := by
    have h1 := Finset.single_le_sum
      (s := (Finset.univ : Finset E)) (f := fun j => |q.charge v j - p.charge v j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ i, |q.charge v i - p.charge v i|) ≤ C := Finset.single_le_sum
      (s := (Finset.univ : Finset V))
      (f := fun j => ∑ i, |q.charge j i - p.charge j i|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ v)
    exact (h1.trans h2).trans (by dsimp only [B]; linarith)
  have hpath := mesh_of_lipschitz (step := G.Step k) (fun t _ _ => segment p q t) hB hε
    (fun s t hs hs' ht ht' hd => ⟨h s hs hs', h t ht ht', by
      constructor
      · intro i b
        exact ((mix_dist _ _ _ _).le.trans
          (mul_le_mul_of_nonneg_right (hb₁ i b) (abs_nonneg _))).trans_lt hd
      · intro v i
        exact ((mix_dist _ _ _ _).le.trans
          (mul_le_mul_of_nonneg_right (hb₂ v i) (abs_nonneg _))).trans_lt hd⟩)
  simpa using hpath

def preload (k : ℚ) (a b : E → Bool) : Point E V where
  toggle := (G.corner k a).toggle
  charge v i := max ((G.corner k a).charge v i) ((G.corner k b).charge v i)

omit [Fintype V] in
private theorem preload_lawful {a b : E → Bool} (h : G.Flip a b) :
    G.Lawful k (G.preload k a b) := by
  obtain ⟨ha, hb, e, he⟩ := h
  refine ⟨G.toggle_sum_corner a, ?_, ?_⟩
  · intro i side ht
    have hs : a i = side := by
      by_contra hs
      apply ht
      simp [preload, corner, hs]
    have hval (o : E → Bool) : (G.corner k o).charge (G.tail i side) i ≤ G.weight i := by
      change (if G.tail i (o i) = G.tail i side then G.weight i else 0) ≤ G.weight i
      split_ifs
      · exact le_rfl
      · exact (G.weight_pos i).le
    apply le_antisymm (max_le (hval a) (hval b))
    exact (show G.weight i = (G.corner k a).charge (G.tail i side) i by
      simp [corner, hs]).le.trans (le_max_left _ _)
  · intro v
    have hw (i : E) (o : E → Bool) : 0 ≤ (G.corner k o).charge v i := by
      simp [corner, apply_ite, (G.weight_pos i).le]
    simp only [preload, abs_of_nonneg ((hw _ a).trans (le_max_left _ _))]
    by_cases hv : G.tail e (b e) = v
    · convert hb v using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = e
      · subst i
        by_cases ha' : G.tail e (a e) = v <;> simp [corner, hv, ha', (G.weight_pos e).le]
      · simp [corner, he i hi]
    · convert ha v using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = e
      · subst i
        by_cases ha' : G.tail e (a e) = v <;> simp [corner, hv, ha', (G.weight_pos e).le]
      · simp [corner, he i hi]

omit [DecidableEq E] [DecidableEq V] [Fintype V] in
private theorem segment_lawful {p q : Point E V} (hp : G.Lawful k p) (hq : G.Lawful k q)
    (h : p.toggle = q.toggle ∨ p.charge = q.charge)
    {t : ℚ} (ht : 0 ≤ t) (ht' : t ≤ 1) : G.Lawful k (segment p q t) := by
  refine ⟨fun i => ?_, fun i b hb => ?_, fun v => ?_⟩
  · change mix (p.toggle i false) (q.toggle i false) t +
      mix (p.toggle i true) (q.toggle i true) t = k
    calc
      _ = mix (p.toggle i false + p.toggle i true) (q.toggle i false + q.toggle i true) t := by
        unfold mix; ring
      _ = k := by rw [hp.1, hq.1, mix_self]
  · rcases h with htog | hcharge
    · have hpt : p.toggle i b ≠ 0 := by simpa [segment, ← htog, mix_self] using hb
      simp [segment, hp.2.1 i b hpt, hq.2.1 i b (by rwa [← htog]), mix_self]
    · have hsome : p.toggle i b ≠ 0 ∨ q.toggle i b ≠ 0 := by
        by_contra hn
        push_neg at hn
        simp [segment, mix, hn.1, hn.2] at hb
      have hc : p.charge (G.tail i b) i = G.weight i :=
        hsome.elim (hp.2.1 i b) (fun hq' => by rw [hcharge, hq.2.1 i b hq'])
      simp [segment, ← hcharge, hc, mix_self]
  · calc
      _ ≤ ∑ i, mix |p.charge v i| |q.charge v i| t := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [segment, mix, abs_mul, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht')] using
          abs_add_le ((1 - t) * p.charge v i) (t * q.charge v i)
      _ ≤ _ := by
        simp only [mix, Finset.sum_add_distrib, ← Finset.mul_sum]
        exact mix_le (hp.2.2 v) (hq.2.2 v) ht ht'

omit [Fintype V] in
/-- The three affine pieces for one flip, before any mesh is chosen. -/
theorem flip_segments_lawful {a b : E → Bool} (h : G.Flip a b) :
    (∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      G.Lawful k (segment (G.corner k a) (G.preload k a b) t)) ∧
    (∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      G.Lawful k (segment (G.preload k a b) (G.preload k b a) t)) ∧
    (∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      G.Lawful k (segment (G.preload k b a) (G.corner k b) t)) := by
  have hf : G.Flip b a := ⟨h.2.1, h.1, h.2.2.imp (fun _ hi j hj => (hi j hj).symm)⟩
  have ha := G.corner_lawful (k := k) h.1
  have hb := G.corner_lawful (k := k) h.2.1
  have hc := G.preload_lawful (k := k) h
  have hd := G.preload_lawful (k := k) hf
  have he : (G.preload k a b).charge = (G.preload k b a).charge := by
    funext v i
    exact max_comm _ _
  exact ⟨fun _ => G.segment_lawful ha hc (.inl rfl),
    fun _ => G.segment_lawful hc hd (.inr he),
    fun _ => G.segment_lawful hd hb (.inl rfl)⟩

theorem flip_has_mesh {a b : E → Bool} (h : G.Flip a b) {ε : ℚ} (hε : 0 < ε) :
    G.Chain k ε (G.corner k a) (G.corner k b) := by
  obtain ⟨h₁, h₂, h₃⟩ := G.flip_segments_lawful h
  exact (G.segment_mesh h₁ hε).trans ((G.segment_mesh h₂ hε).trans (G.segment_mesh h₃ hε))

theorem chain_of_flips {a b : E → Bool} (h : G.Flips a b) {ε : ℚ} (hε : 0 < ε) :
    G.Chain k ε (G.corner k a) (G.corner k b) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (G.flip_has_mesh hstep hε)

end Graph

/-- An ordinary minimum-inflow-two network. End labels keep both incidences
of a loop distinct. Only the degree and weight bounds of AND/OR networks
are needed for the reduction. -/
structure Network (E V : Type*) [Fintype E] [DecidableEq V] where
  ends : E → Bool → V
  weights : E → ℚ
  weights_pos : ∀ i, 0 < weights i
  weights_le : ∀ i, weights i ≤ 2
  degree_le : ∀ v, (∑ i, ((if ends i false = v then weights i else 0) +
    (if ends i true = v then weights i else 0))) ≤ 6

namespace Network

variable (N : Network E V)

def degree (v : V) : ℚ :=
  ∑ i, ((if N.ends i false = v then N.weights i else 0) +
    (if N.ends i true = v then N.weights i else 0))

def inflow (a : E → Bool) (v : V) : ℚ :=
  ∑ i, if N.ends i (!(a i)) = v then N.weights i else 0

def Legal (a : E → Bool) : Prop := ∀ v, 2 ≤ N.inflow a v

def Flip (a b : E → Bool) : Prop :=
  N.Legal a ∧ N.Legal b ∧ ∃ i, a i ≠ b i ∧ ∀ j ≠ i, a j = b j

abbrev Flips := Relation.ReflTransGen N.Flip

def scaled : Graph E V :=
  ⟨N.ends, fun i => N.weights i / 8, fun v => (N.degree v - 2) / 8,
    fun i => div_pos (N.weights_pos i) (by norm_num)⟩

omit [DecidableEq E] in
theorem weights_bound (i : E) : N.scaled.weight i ≤ 1/2 := by
  change N.weights i / 8 ≤ 1/2
  linarith [N.weights_le i]

omit [DecidableEq E] in
theorem capacity_bound (v : V) : N.scaled.capacity v ≤ 1/2 := by
  change (N.degree v - 2) / 8 ≤ 1/2
  have hv : N.degree v ≤ 6 := N.degree_le v
  linarith

omit [DecidableEq E] in
theorem legal_iff_scaled (a : E → Bool) : N.Legal a ↔ N.scaled.Legal a := by
  have he (v : V) : N.scaled.Load a v + N.inflow a v / 8 = N.degree v / 8 := by
    unfold Graph.Load scaled inflow degree
    simp only [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases a i <;> simp only [Bool.not_true, Bool.not_false, add_mul] <;>
      by_cases hf : N.ends i false = v <;> by_cases ht : N.ends i true = v <;>
      simp [hf, ht, add_comm]
  constructor
  · intro h v
    change N.scaled.Load a v ≤ (N.degree v - 2) / 8
    linarith [he v, h v]
  · intro h v
    have hv : N.scaled.Load a v ≤ (N.degree v - 2) / 8 := h v
    linarith [he v]

omit [DecidableEq E] in
theorem flips_iff_scaled (a b : E → Bool) : N.Flips a b ↔ N.scaled.Flips a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
      obtain ⟨hx, hy, i, _, hi⟩ := hstep
      exact ih.tail ⟨(N.legal_iff_scaled _).mp hx, (N.legal_iff_scaled _).mp hy, i, hi⟩
  · intro h
    induction h with
    | refl => exact .refl
    | @tail x y _ hstep ih =>
      obtain ⟨hx, hy, i, hi⟩ := hstep
      by_cases hp : x i = y i
      · have he : x = y := by
          funext j
          by_cases hj : j = i
          · simpa only [hj] using hp
          · exact hi j hj
        exact he ▸ ih
      · exact ih.tail ⟨(N.legal_iff_scaled _).mpr hx, (N.legal_iff_scaled _).mpr hy, i, hp, hi⟩

end Network

end MovingProjection.ConstraintLogic
