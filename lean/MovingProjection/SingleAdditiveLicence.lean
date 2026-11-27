import MovingProjection.BinaryParity
import MovingProjection.ConstraintLogic
import MovingProjection.EventExperiments

/-! One two-word licence at a fixed profile is sufficient for
constraint-logic configuration reachability. -/

namespace MovingProjection.SingleAdditiveLicence

open scoped BigOperators
open ConstraintLogic

variable {E V X : Type*} [Fintype E] [Fintype V] [Fintype X]
  [DecidableEq E] [DecidableEq V] [DecidableEq X] [Nonempty X]

abbrev Mark (E V : Type*) := Unit ⊕ (Bool ⊕ (E ⊕ V))
abbrev Probe (E : Type*) := Option E
abbrev Licence (E : Type*) := Unit ⊕ (E × Bool)
abbrev Publication (E V : Type*) := Probe E ⊕ ((E × Probe E) ⊕ V)

def leftMark : Mark E V := .inl ()
def toggle (b : Bool) : Mark E V := .inr (.inl b)
def selector (i : E) : Mark E V := .inr (.inr (.inl i))
def vertex (v : V) : Mark E V := .inr (.inr (.inr v))

def floor (E V : Type*) [Fintype E] [Fintype V] : ℚ :=
  1 / ((Fintype.card E : ℚ) + Fintype.card V + 4)

def amplitude (E : Type*) [Fintype E] : ℚ := 1 / (4 * (Fintype.card (Probe E) : ℚ))

omit [DecidableEq E] [DecidableEq V] in
theorem floor_pos : 0 < floor E V := by unfold floor; positivity

omit [DecidableEq E] in
theorem amplitude_pos : 0 < amplitude E := by
  unfold amplitude
  rw [Fintype.card_option, Nat.cast_succ]
  positivity

def rates : Mark E V → ℚ
  | .inl _ => 2 * floor E V
  | .inr _ => floor E V

omit [DecidableEq E] [DecidableEq V] in
theorem rates_sum : ∑ m, (rates (E := E) (V := V) m) = 1 := by
  simp only [Fintype.sum_sum_type, rates, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_sum, Fintype.card_bool, Fintype.card_unit, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  unfold floor
  have hn : (Fintype.card E : ℚ) + (Fintype.card V : ℚ) + 4 ≠ 0 := by positivity
  field_simp
  ring

variable (G : Graph E V)

/-- The empty suffix gives a duration-one widened licence. -/
def commonTail (short : Bool) : List (Mark E V) := if short then [] else [leftMark]

def pair (g : Licence E) (short : Bool := false) : TimedPair (Mark E V) 3 :=
  match g with
  | .inl _ => ⟨leftMark, toggle false, commonTail short, commonTail short, rfl, by
      cases short <;> simp [commonTail]⟩
  | .inr (i,b) => ⟨selector i, selector i, [toggle b, vertex (G.tail i b)],
      [toggle b, selector i], rfl, by simp⟩

private def extra (short : Bool) : SecondWord (pair G (.inl ()) short) :=
  ⟨toggle true :: commonTail short, rfl, by simp [pair, TimedPair.right, toggle]⟩

def second (g : Licence E) (short : Bool := false) : Option (SecondWord (pair G g short)) :=
  match g with
  | .inl _ => some (extra G short)
  | .inr _ => none

def audit : Publication E V → AuditQuery (Mark E V) (Probe E) 3
  | .inl j => .calibration leftMark j (amplitude E / 2)
  | .inr (.inl (i,j)) => .calibration (selector i) j (if j = some i then G.weight i else 0)
  | .inr (.inr v) => .calibration (vertex v) none (1/2 - G.capacity v)

def instrument (B : ParityBasis (Probe E) X) (short : Bool := false) :
    EventExperiments (Mark E V) (Probe E) X Unit (Licence E) (Publication E V) where
  native := {
    parity := B
    weights := fun _ => 1
    weights_pos := fun _ => zero_lt_one
    weights_unit := by simp
    reversal := id
    reversal_involutive := fun _ => rfl
    δ := floor E V
    δ_pos := floor_pos
    κ := 1/2
    κ_lt_one := by norm_num
    horizon := 3
    license := fun g => pair G g short
    audit := audit G
    policy := fun held => held = Finset.univ
  }
  second := fun g => second G g short

abbrev State (B : ParityBasis (Probe E) X) (short : Bool := false) := (instrument G B short).State 0

def profile : Capabilities (Mark E V) X Unit (Licence E) (Publication E V) 0 :=
  ⟨OrderDual.toDual Set.univ, fun _ => OrderDual.toDual ⊤, Finset.univ, Finset.univ⟩

omit [DecidableEq V] [DecidableEq X] [Nonempty X] in
theorem exactly_one (B : ParityBasis (Probe E) X) (short : Bool := false) :
    ∃! g, ((instrument G B short).second g).isSome = true := by
  refine ⟨.inl (), rfl, ?_⟩
  intro g hg
  rcases g with (⟨⟩ | g)
  · rfl
  · exact False.elim (Bool.noConfusion hg)

omit [DecidableEq X] in
private theorem weighted_kernel_iff {J : Type*} [Fintype J] [DecidableEq J]
    (B : ParityBasis J X) (s a b : J → ℚ) (p q r : ℚ) :
    (∀ x y, p * B.kernel s x y = q * B.kernel a x y + r * B.kernel b x y) ↔
      p = q + r ∧ ∀ i, p * s i = q * a i + r * b i := by
  constructor
  · intro h
    let x : X := Classical.choice inferInstance
    constructor
    · have he := Finset.sum_congr (s₁ := (Finset.univ : Finset X)) rfl (fun y _ => h x y)
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, B.kernel_row_sum, mul_one] using he
    · intro i
      have he := Finset.sum_congr (s₁ := (Finset.univ : Finset X)) rfl
        (fun y _ => congrArg (fun z : ℚ => z * B.value i y) (h x y))
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, B.kernel_response] at he
      have hv : B.value i x ≠ 0 := by
        intro hz
        have h := B.abs_eq_one i x
        simp [hz] at h
      exact mul_right_cancel₀ hv (by simpa only [add_mul, mul_assoc] using he)
  · rintro ⟨hp, hi⟩ x y
    have hn : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    unfold ParityBasis.kernel
    field_simp
    have hs : p * (∑ i, s i * B.value i x * B.value i y) =
        q * (∑ i, a i * B.value i x * B.value i y) +
          r * (∑ i, b i * B.value i x * B.value i y) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [← mul_assoc, hi, add_mul]
    simp only [mul_add, mul_one]
    rw [hs]
    linarith

/-- A single measured word-versus-pair comparison gives one mass
equation and one scalar coefficient equation for each probe. -/
theorem joint_words_iff {M J R : Type*} [Fintype J] [DecidableEq J] [Fintype R] [Nonempty R]
    (B : ParityBasis J X) (a : PhysicalLaw M J X R)
    (hr : ∀ m x y u, ∑ v, a.register m x y u v = 1)
    (m n p : M) (u v w : List M) :
    (∀ x y, nativeWordEndpoint (a.marked B) (m :: u) x y =
      nativeWordEndpoint (a.marked B) (n :: v) x y +
      nativeWordEndpoint (a.marked B) (p :: w) x y) ↔
    let weight l := (l.map a.rate).prod
    let response l i := (l.map (fun q => a.spectrum (q,i))).prod
    weight (m :: u) = weight (n :: v) + weight (p :: w) ∧
      ∀ i, weight (m :: u) * response (m :: u) i =
        weight (n :: v) * response (n :: v) i + weight (p :: w) * response (p :: w) i := by
  have hf (q : M) (l : List M) (x : X × R) (y : X) :
      nativeWordEndpoint (a.marked B) (q :: l) x y =
        (((q :: l).map a.rate).prod) *
          B.kernel (fun i => ((q :: l).map (fun z => a.spectrum (z,i))).prod) x.1 y := by
    simpa only [PhysicalLaw.marked, projectedWordEndpoint_nonempty,
      ParityBasis.nonemptyWord_eq] using
      nativeWordEndpoint_factor B (fun q i => a.spectrum (q,i))
        a.rate a.register hr (q :: l) x y
  simp_rw [hf]
  rw [← weighted_kernel_iff B]
  constructor
  · exact fun h x y => h (x, Classical.choice inferInstance) y
  · exact fun h x y => h x.1 y

omit [Fintype V] [DecidableEq V] in
private theorem special_measurement_iff (B : ParityBasis (Probe E) X)
    (a : PhysicalLaw (Mark E V) (Probe E) X Unit) (short : Bool)
    (hr : ∀ m x y u, ∑ v, a.register m x y u v = 1)
    (hL : a.rate leftMark ≠ 0) (hα : ∀ i, a.spectrum (leftMark,i) ≠ 0) :
    (∀ x y, nativeWordEndpoint (a.marked B) (leftMark :: commonTail short) x y =
      nativeWordEndpoint (a.marked B) (toggle false :: commonTail short) x y +
      nativeWordEndpoint (a.marked B) (toggle true :: commonTail short) x y) ↔
    (a.rate leftMark = a.rate (toggle false) + a.rate (toggle true)) ∧
    ∀ i, a.rate leftMark * a.spectrum (leftMark,i) =
      a.rate (toggle false) * a.spectrum (toggle false,i) +
      a.rate (toggle true) * a.spectrum (toggle true,i) := by
  rw [joint_words_iff B a hr]
  cases short
  · simp only [commonTail, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    constructor
    · rintro ⟨hm, hs⟩
      refine ⟨mul_right_cancel₀ hL (by simpa only [add_mul] using hm), fun i => ?_⟩
      have hb := hs i
      apply mul_right_cancel₀ (mul_ne_zero hL (hα i))
      linear_combination hb
    · rintro ⟨hm, hs⟩
      refine ⟨by linear_combination a.rate leftMark * hm, fun i => ?_⟩
      linear_combination (a.rate leftMark * a.spectrum (leftMark,i)) * hs i
  · simp [commonTail]

omit [DecidableEq E] [DecidableEq V] in
private theorem rates_forced (θ : Mark E V → ℚ)
    (hs : ∑ m, θ m = 1) (hl : ∀ m, floor E V ≤ θ m)
    (he : θ leftMark = θ (toggle false) + θ (toggle true)) :
    θ = rates := by
  have hb (m : Mark E V) : rates m ≤ θ m := by
    cases m with
    | inl u =>
      cases u
      change 2 * floor E V ≤ θ (leftMark : Mark E V)
      linarith [hl (toggle false), hl (toggle true)]
    | inr x => exact hl _
  have hz : ∑ m, (θ m - rates m) = 0 := by rw [Finset.sum_sub_distrib, hs, rates_sum, sub_self]
  funext m
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun m => θ m - rates m)
    (fun j _ => sub_nonneg.mpr (hb j)) (Finset.mem_univ m)
  rw [hz] at h
  linarith [hb m]

variable {G} {B : ParityBasis (Probe E) X} {short : Bool}

omit [DecidableEq V] [DecidableEq X] [Nonempty X] in
private theorem base_pair_singleton (i : E) (b : Bool) :
    (instrument G B short).base.license (.inr (i,b)) = pair G (.inr (i,b)) := rfl

omit [Nonempty X] in
private theorem calibration (s : State G B short) (hp : s.val.profile = profile)
    (e : Publication E V) {m : Mark E V} {j : Probe E} {v : ℚ}
    (h : audit G e = .calibration m j v) :
    s.val.law.spectrum (m,j) = v :=
  (instrument G B short).base.calibration_value s.val
    (by rw [hp]; exact Finset.mem_univ e) h

omit [Nonempty X] in
private theorem left_calibrated (s : State G B short) (hp : s.val.profile = profile) (j : Probe E) :
    s.val.law.spectrum (leftMark,j) = amplitude E / 2 :=
  calibration s hp (.inl j) rfl

omit [Nonempty X] in
private theorem selector_calibrated (s : State G B short) (hp : s.val.profile = profile)
    (i : E) (j : Probe E) :
    s.val.law.spectrum (selector i,j) = if j = some i then G.weight i else 0 :=
  calibration s hp (.inr (.inl (i,j))) rfl

omit [DecidableEq E] [DecidableEq V] in
private theorem toggle_sum_iff {x y : ℚ} :
    (2 * floor E V) * (amplitude E / 2) = floor E V * x + floor E V * y ↔
      x + y = amplitude E := by
  rw [← mul_add, show 2 * floor E V * (amplitude E / 2) = floor E V * amplitude E by ring]
  exact (mul_right_inj' (floor_pos (E := E) (V := V)).ne').trans eq_comm

private theorem measured_forces_rates (s : State G B short) (hp : s.val.profile = profile) :
    s.val.law.rate = rates ∧
    ∀ j, s.val.law.spectrum (toggle false,j) + s.val.law.spectrum (toggle true,j) =
      amplitude E := by
  have hj (x : X × Unit) (y : X) := s.property (.inl ()) (by rw [hp]; exact Finset.mem_univ _)
    _ rfl x y
  have hL := (floor_pos (E := E) (V := V)).trans_le (s.val.legal.2.2.1.1 leftMark)
  have hα (j : Probe E) : s.val.law.spectrum (leftMark,j) ≠ 0 := by
    rw [left_calibrated s hp j]
    exact (div_pos (amplitude_pos (E := E)) (by norm_num)).ne'
  have hs := (special_measurement_iff B s.val.law short s.val.legal.2.2.2.2.1.2.1 hL.ne' hα).mp hj
  have hr := rates_forced _ s.val.legal.2.2.1.2.1 s.val.legal.2.2.1.1 hs.1
  refine ⟨hr, fun j => (toggle_sum_iff (E := E) (V := V)).mp ?_⟩
  have hi := hs.2 j
  rw [hr, left_calibrated s hp j] at hi
  exact hi

def decode (s : State G B short) : Graph.Point E V where
  toggle i b := s.val.law.spectrum (toggle b,some i)
  charge v i := s.val.law.spectrum (vertex v,some i)

private theorem decode_lawful (s : State G B short) (hp : s.val.profile = profile)
    (hc : ∀ v, G.capacity v ≤ 1/2) :
    G.Lawful (amplitude E) (decode s) := by
  refine ⟨fun i => (measured_forces_rates s hp).2 (some i), ?_, ?_⟩
  · intro i b hb
    let D := (instrument G B short).base
    have hs := (D.license_measured s.val
      (g := .inr (i,b)) (by rw [hp]; exact Finset.mem_univ _)).2
    dsimp only [D] at hs
    rw [base_pair_singleton] at hs
    have he := (B.word_identity_iff (fun m j => s.val.law.spectrum (m,j)) _ _ _ _).mp hs (some i)
    simp only [pair, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      selector_calibrated s hp i (some i), if_true] at he
    have hm : G.weight i * s.val.law.spectrum (toggle b,some i) ≠ 0 :=
      mul_ne_zero (G.weight_pos i).ne' hb
    exact mul_left_cancel₀ hm (by simpa only [mul_assoc] using he)
  · intro v
    have hs := spectrum_budget s.val.legal.2.2.2.1 (vertex v)
    rw [Fintype.sum_option, calibration s hp (.inr (.inr v)) rfl,
      abs_of_nonneg (sub_nonneg.mpr (hc v))] at hs
    change _ ≤ (1/2 : ℚ) at hs
    change (∑ i, |s.val.law.spectrum (vertex v,some i)|) ≤ G.capacity v
    linarith

private def clip (k x : ℚ) := max (min x k) 0

private theorem clip_nonneg (k x : ℚ) : 0 ≤ clip k x := le_max_right _ _

private theorem clip_le {k : ℚ} (hk : 0 ≤ k) (x : ℚ) : clip k x ≤ k :=
  max_le (min_le_right _ _) hk

private theorem clip_id {k x : ℚ} (h₀ : 0 ≤ x) (h₁ : x ≤ k) : clip k x = x := by
  simp [clip, min_eq_left h₁, max_eq_left h₀]

private theorem clip_sum {k x y : ℚ} (hk : 0 ≤ k) (hs : x + y = k) :
    clip k x + clip k y = k := by
  by_cases h₀ : x ≤ 0
  · have hy : k ≤ y := by linarith
    simp [clip, min_eq_left (h₀.trans hk), max_eq_right h₀, min_eq_right hy, max_eq_left hk]
  · by_cases h₁ : k ≤ x
    · have hy : y ≤ 0 := by linarith
      simp [clip, min_eq_right h₁, max_eq_left hk, min_eq_left (hy.trans hk), max_eq_right hy]
    · rw [clip_id (by linarith) (by linarith), clip_id (by linarith) (by linarith)]
      exact hs

private theorem clip_dist (k x y : ℚ) : |clip k x - clip k y| ≤ |x - y| := by
  unfold clip
  apply (abs_max_sub_max_le_abs _ _ _).trans
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (x-y))] using
    abs_min_sub_min_le_max x k y k

def encodeSpectrum (p : Graph.Point E V) : Mark E V × Probe E → ℚ
  | (.inl _, _) => amplitude E / 2
  | (.inr (.inl b), some i) => clip (amplitude E) (p.toggle i b)
  | (.inr (.inl b), none) => if b then 0 else amplitude E
  | (.inr (.inr (.inl i)), j) => if j = some i then G.weight i else 0
  | (.inr (.inr (.inr v)), some i) => p.charge v i
  | (.inr (.inr (.inr v)), none) => 1/2 - G.capacity v

def encodeLaw (G : Graph E V) (p : Graph.Point E V) : PhysicalLaw (Mark E V) (Probe E) X Unit :=
  ⟨rates, encodeSpectrum (G := G) p, fun _ _ _ _ _ => 1⟩

omit [Fintype V] [DecidableEq V] in
private theorem encoded_toggle_bounds (p : Graph.Point E V) (b : Bool) (j : Probe E) :
    0 ≤ encodeSpectrum (G := G) p (toggle b,j) ∧
      encodeSpectrum (G := G) p (toggle b,j) ≤ amplitude E := by
  have hk := amplitude_pos (E := E)
  cases j with
  | none => cases b <;> simp [toggle, encodeSpectrum, hk.le]
  | some i => exact ⟨clip_nonneg _ _, clip_le hk.le _⟩

omit [Fintype V] [DecidableEq V] in
private theorem encoded_toggle_sum (p : Graph.Point E V) (hp : G.Lawful (amplitude E) p)
    (j : Probe E) : encodeSpectrum (G := G) p (toggle false,j) +
      encodeSpectrum (G := G) p (toggle true,j) = amplitude E := by
  cases j with
  | none => simp [toggle, encodeSpectrum]
  | some i => exact clip_sum (amplitude_pos (E := E)).le (hp.1 i)

omit [Fintype V] [DecidableEq V] in
private theorem encoded_budget (p : Graph.Point E V) (hp : G.Lawful (amplitude E) p)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) (m : Mark E V) :
    ∑ j, |encodeSpectrum (G := G) p (m,j)| ≤ 1/2 := by
  have hk := amplitude_pos (E := E)
  have ht : (Fintype.card (Probe E) : ℚ) * amplitude E = 1/4 := by
    unfold amplitude
    have hn : (Fintype.card (Probe E) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rcases m with (_ | b | i | v)
  · simp only [encodeSpectrum, abs_of_nonneg (by positivity : 0 ≤ amplitude E / 2),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  · calc
      _ ≤ ∑ j : Probe E, amplitude E := Finset.sum_le_sum (fun j _ => by
        change |encodeSpectrum (G := G) p (toggle b,j)| ≤ amplitude E
        rw [abs_of_nonneg (encoded_toggle_bounds (G := G) p b j).1]
        exact (encoded_toggle_bounds (G := G) p b j).2)
      _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ht]
        norm_num
  · simpa only [encodeSpectrum, abs_ite, abs_zero, abs_of_pos (G.weight_pos i),
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using hw i
  · rw [Fintype.sum_option]
    simp only [encodeSpectrum, abs_of_nonneg (sub_nonneg.mpr (hc v))]
    linarith [hp.2.2 v]

private theorem encoded_character (p : Graph.Point E V) (hp : G.Lawful (amplitude E) p)
    (i : E) (b : Bool) (j : Probe E) :
    (routeCharacterTest (pair G (.inr (i,b))).left (pair G (.inr (i,b))).right j).holds
      (encodeSpectrum (G := G) p) := by
  simp only [MonomialTest.holds, routeCharacterTest, one_mul,
    character_monomial _ _ (fun m j => encodeSpectrum (G := G) p (m,j))]
  simp only [pair, TimedPair.left, TimedPair.right, selector, vertex, toggle,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  by_cases h : j = some i
  · subst j
    by_cases hz : p.toggle i b = 0
    · simp [encodeSpectrum, clip, hz, min_eq_left (amplitude_pos (E := E)).le]
    · simp [encodeSpectrum, hp.2.1 i b hz]
  · simp [encodeSpectrum, h]

omit [DecidableEq E] [DecidableEq V] in
private theorem rates_ge_floor (m : Mark E V) : floor E V ≤ rates m := by
  cases m with
  | inl u =>
    change floor E V ≤ 2 * floor E V
    linarith [floor_pos (E := E) (V := V)]
  | inr u => exact le_rfl

omit [DecidableEq E] [DecidableEq V] in
private theorem rates_between (m : Mark E V) : 0 ≤ rates m ∧ rates m ≤ 1 := by
  have h (m : Mark E V) : 0 ≤ rates m :=
    (floor_pos (E := E) (V := V)).le.trans (rates_ge_floor m)
  refine ⟨h m, ?_⟩
  rw [← rates_sum (E := E) (V := V)]
  exact Finset.single_le_sum (fun m _ => h m) (Finset.mem_univ m)

omit [Fintype V] [DecidableEq V] in
private theorem encoded_calibration (p : Graph.Point E V) (e : Publication E V) :
    ∃ m j c, audit G e = .calibration m j c ∧ encodeSpectrum (G := G) p (m,j) = c := by
  rcases e with (j | ⟨i,j⟩ | v)
  · exact ⟨leftMark, j, _, rfl, rfl⟩
  · exact ⟨selector i, j, _, rfl, rfl⟩
  · exact ⟨vertex v, none, _, rfl, rfl⟩

omit [DecidableEq X] [Nonempty X] in
set_option maxHeartbeats 800000 in
private theorem encode_legal (p : Graph.Point E V) (hp : G.Lawful (amplitude E) p)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) :
    (instrument G B short).base.protocol.legal profile (encodeLaw G p) := by
  let D := (instrument G B short).base
  refine ⟨fun _ _ _ => le_rfl, rfl, ⟨rates_ge_floor, rates_sum, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro test ht
    change test ∈ D.protocol.checks.rateTests Finset.univ Finset.univ at ht
    simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at ht
    rcases ht with ⟨g, _, hg⟩ | ⟨e, _, he⟩
    · change test ∈ [⟨routeRateRow (D.license g).left (D.license g).right, 1⟩] at hg
      obtain rfl := List.mem_singleton.mp hg
      apply (route_rate_compile _ _ _ _).mpr
      rcases g with (⟨⟩ | ⟨i,b⟩)
      · change (List.map rates (leftMark :: commonTail short)).prod =
            1 * (List.map rates (leftMark :: commonTail short)).prod
        exact (one_mul _).symm
      · change (List.map rates [selector i,toggle b,vertex (G.tail i b)]).prod =
            1 * (List.map rates [selector i,toggle b,selector i]).prod
        simp [rates, selector, toggle, vertex]
    · rcases e with (j | ⟨i,j⟩ | v) <;> cases he
  · intro test ht
    change test ∈ D.protocol.checks.spectralTests Finset.univ Finset.univ at ht
    simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap] at ht
    rcases ht with (hr | ⟨g, _, hg⟩) | ⟨e, _, he⟩
    · change test ∈ Finset.univ.toList.map (reversalTest (id : Mark E V → Mark E V)) at hr
      obtain ⟨⟨m,i⟩,_,rfl⟩ := List.mem_map.mp hr
      simp [reversalTest, MonomialTest.holds]
    · change test ∈ Finset.univ.toList.map
        (routeCharacterTest (D.license g).left (D.license g).right) at hg
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      rcases g with (⟨⟩ | ⟨e,b⟩)
      · change (routeCharacterTest (leftMark :: commonTail short) (leftMark :: commonTail short) i).holds _
        simp [routeCharacterTest, MonomialTest.holds]
      · exact encoded_character p hp e b i
    · obtain ⟨m,i,c,ha,hc⟩ := encoded_calibration (G := G) p e
      have ha' : D.audit e = .calibration m i c := ha
      dsimp only [NativeExperiments.protocol] at he
      rw [ha'] at he
      obtain rfl := List.mem_singleton.mp he
      change monomial (pointExponent (m,i)) (encodeSpectrum (G := G) p) =
        c * monomial (fun _ => 0) (encodeSpectrum (G := G) p)
      rw [pointMonomial, hc]
      simp [monomial]
  · intro budget hbudget
    unfold spectrumBudgets at hbudget
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hbudget
    change (∑ i ∈ Finset.univ.map _, |(encodeLaw (X := X) G p).spectrum i|) ≤ 1/2
    rw [Finset.sum_map]
    exact encoded_budget p hp hw hc m
  · simp [RegisterValid, encodeLaw, EventExperiments.base, instrument, NativeExperiments.protocol]
  · ext e
    simp [Protocol.fiber, profile, registerMask, encodeLaw]

omit [DecidableEq V] in
private theorem encode_holds (p : Graph.Point E V) (hp : G.Lawful (amplitude E) p) :
    (instrument G B short).holds profile (encodeLaw G p) := by
  intro g _ w hg
  cases g with
  | inl u =>
    cases u
    change some (extra G short) = some w at hg
    have hw := Option.some.inj hg
    subst w
    have hf : (encodeLaw (X := X) G p).rate leftMark ≠ 0 :=
      ((floor_pos (E := E) (V := V)).trans_le (rates_ge_floor leftMark)).ne'
    have hs (j : Probe E) : (encodeLaw (X := X) G p).spectrum (leftMark,j) ≠ 0 :=
      (div_pos (amplitude_pos (E := E)) (by norm_num : (0 : ℚ) < 2)).ne'
    apply (special_measurement_iff B _ short (by intros; simp [encodeLaw]) hf hs).mpr
    constructor
    · change 2 * floor E V = floor E V + floor E V
      ring
    · intro j
      exact (toggle_sum_iff (E := E) (V := V)).mpr (encoded_toggle_sum p hp j)
  | inr g =>
    change none = some w at hg
    cases hg

noncomputable def encode (B : ParityBasis (Probe E) X) (p : Graph.Point E V)
    (hp : G.Lawful (amplitude E) p) (hw : ∀ i, G.weight i ≤ 1/2)
    (hc : ∀ v, G.capacity v ≤ 1/2) : State G B short :=
  ⟨⟨profile, encodeLaw G p, encode_legal p hp hw hc⟩, encode_holds p hp⟩

omit [Fintype V] [DecidableEq V] in
private theorem encode_spectrum_near {p q : Graph.Point E V} {η : ℚ}
    (hη : 0 < η) (h : Graph.Near η p q) (mj : Mark E V × Probe E) :
    |encodeSpectrum (G := G) p mj - encodeSpectrum (G := G) q mj| < η := by
  rcases mj with ⟨(_ | b | i | v), (_ | j)⟩ <;> try simpa only [encodeSpectrum, sub_self, abs_zero] using hη
  · exact (clip_dist (amplitude E) (p.toggle j b) (q.toggle j b)).trans_lt (h.1 j b)
  · exact h.2 v j

private def smallFor (E : Type*) [Fintype E] (ε : ℚ) := ε / ((Fintype.card (Probe E) : ℚ) + 1)

omit [DecidableEq E] in
private theorem smallFor_pos {ε : ℚ} (hε : 0 < ε) : 0 < smallFor E ε := by
  unfold smallFor
  positivity

omit [DecidableEq V] [DecidableEq X] in
private theorem encode_near {p q : Graph.Point E V} {ε : ℚ} (hε : 0 < ε)
    (h : Graph.Near (smallFor E ε) p q) :
    PhysicalNear B ε (encodeLaw G p) (encodeLaw G q) := by
  rintro m ⟨x, u⟩ ⟨y,v⟩
  let a := fun j => encodeSpectrum (G := G) p (m,j)
  let c := fun j => encodeSpectrum (G := G) q (m,j)
  change |rates m * B.kernel a x y * 1 - rates m * B.kernel c x y * 1| < ε
  rw [mul_one, mul_one, ← mul_sub, abs_mul, abs_of_nonneg (rates_between m).1]
  have hk := B.kernel_sub_le (fun j => (encode_spectrum_near (G := G) (smallFor_pos hε) h (m,j)).le) x y
  refine ((mul_le_of_le_one_left (abs_nonneg _) (rates_between m).2).trans hk).trans_lt ?_
  have he : ((Fintype.card (Probe E) : ℚ) + 1) * smallFor E ε = ε := by
    unfold smallFor
    have hn : (Fintype.card (Probe E) : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  linarith [smallFor_pos (E := E) hε]

private theorem encode_chain {p q : Graph.Point E V}
    (hp : G.Lawful (amplitude E) p) (hq : G.Lawful (amplitude E) q)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2)
    {ε : ℚ} (hε : 0 < ε) (h : G.Chain (amplitude E) (smallFor E ε) p q) :
    (instrument G B short).Chain ε (encode B p hp hw hc) (encode B q hq hw hc) := by
  induction h with
  | refl => exact .refl
  | @tail u v _ hs ih =>
    exact (ih hs.1).tail (Or.inl ⟨rfl, encode_near hε hs.2.2⟩)

def tolerance (E V X : Type*) [Fintype E] [Fintype V] [Fintype X] : ℚ :=
  floor E V * amplitude E / (2 * (Fintype.card (X × Unit) : ℚ) + 1)

omit [DecidableEq E] [DecidableEq V] [DecidableEq X] in
theorem tolerance_pos : 0 < tolerance E V X := by
  unfold tolerance
  have := floor_pos (E := E) (V := V)
  have := amplitude_pos (E := E)
  positivity

private theorem decode_step {s t : State G B short}
    (hs : s.val.profile = profile) (ht : t.val.profile = profile)
    (hc : ∀ v, G.capacity v ≤ 1/2)
    (h : (instrument G B short).Step (tolerance E V X) s t) :
    G.Step (amplitude E) (amplitude E) (decode s) (decode t) := by
  have hn := ((instrument G B short).step_iff_near_of_profile_eq (hs.trans ht.symm)).mp h
  let D := (instrument G B short).base.protocol
  have ht' : D.legal s.val.profile t.val.law := by rw [← ht] at hs; rw [hs]; exact t.val.legal
  have hl := spectralModulus_for_physicalStep (R := Unit) B
    (floor_pos (E := E) (V := V)) (show (1/2 : ℚ) < 1 by norm_num) (amplitude_pos (E := E))
    (p := D.fiber s.val.profile) (ν := D.ν) (rev := D.reverse)
    ⟨s.val.legal.2.2, ht'.2.2, hn⟩
  exact ⟨decode_lawful s hs hc, decode_lawful t ht hc,
    fun i b => hl.2.2 (toggle b,some i), fun v i => hl.2.2 (vertex v,some i)⟩

private theorem decode_chain {s t : State G B short}
    (hs : s.val.profile = profile) (ht : t.val.profile = profile)
    (hc : ∀ v, G.capacity v ≤ 1/2)
    (h : (instrument G B short).Chain (tolerance E V X) s t) :
    G.Chain (amplitude E) (amplitude E) (decode s) (decode t) := by
  induction h with
  | refl => exact .refl
  | @tail u v hu hedge ih =>
    have huv : u.val.profile = profile := le_antisymm
      (ht ▸ hedge.profile_le) (hs ▸ EventExperiments.Chain.profile_le hu)
    exact (ih huv).tail (decode_step huv ht hc hedge)

noncomputable def endpoint (B : ParityBasis (Probe E) X) (a : E → Bool) (ha : G.Legal a)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) : State G B short :=
  encode B (G.corner (amplitude E) a) (G.corner_lawful ha) hw hc

private theorem decode_endpoint (a : E → Bool) (ha : G.Legal a)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) :
    decode (endpoint (short := short) B a ha hw hc) = G.corner (amplitude E) a := by
  suffices (decode (endpoint (short := short) B a ha hw hc)).toggle = (G.corner (amplitude E) a).toggle by
    exact Graph.Point.ext this rfl
  funext i b
  change clip (amplitude E) (if a i = b then amplitude E else 0) =
    if a i = b then amplitude E else 0
  have hk := (amplitude_pos (E := E)).le
  split_ifs
  · exact clip_id hk le_rfl
  · exact clip_id le_rfl hk

theorem endpoints_distinct {a b : E → Bool} (ha : G.Legal a) (hb : G.Legal b)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) (hab : a ≠ b) :
    endpoint (short := short) B a ha hw hc ≠ endpoint (short := short) B b hb hw hc := by
  intro h
  have he := congrArg decode h
  rw [decode_endpoint, decode_endpoint] at he
  have hr := (G.represents_corner (amplitude_pos (E := E)) b b).mpr rfl
  rw [← he] at hr
  exact hab ((G.represents_corner (amplitude_pos (E := E)) a b).mp hr)

theorem chain_iff_flips {a b : E → Bool} (ha : G.Legal a) (hb : G.Legal b)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) :
    (instrument G B short).Chain (tolerance E V X) (endpoint B a ha hw hc) (endpoint B b hb hw hc) ↔
      G.Flips a b := by
  constructor
  · intro h
    have h' := decode_chain (B := B) rfl rfl hc h
    rw [decode_endpoint, decode_endpoint] at h'
    have hk := amplitude_pos (E := E)
    exact G.flips_of_chain hk (G.corner_lawful ha)
      ((G.represents_corner hk a a).mpr rfl) ((G.represents_corner hk b b).mpr rfl) h'
  · intro h
    exact encode_chain (G.corner_lawful ha) (G.corner_lawful hb) hw hc tolerance_pos
      (G.chain_of_flips h (smallFor_pos tolerance_pos))

theorem fine_iff_flips {a b : E → Bool} (ha : G.Legal a) (hb : G.Legal b)
    (hw : ∀ i, G.weight i ≤ 1/2) (hc : ∀ v, G.capacity v ≤ 1/2) :
    (instrument G B short).Factorable (endpoint B a ha hw hc) (endpoint B b hb hw hc) ↔ G.Flips a b := by
  constructor
  · intro h
    exact (chain_iff_flips (short := short) ha hb hw hc).mp (h _ tolerance_pos)
  · intro h ε hε
    exact encode_chain (G.corner_lawful ha) (G.corner_lawful hb) hw hc hε
      (G.chain_of_flips h (smallFor_pos hε))

abbrev BinaryBase (E : Type*) [Fintype E] :=
  BinaryParity.Base (BinaryParity.dimension (Probe E))

noncomputable def nclInstrument (N : Network E V) (short : Bool := false) :
    EventExperiments (Mark E V) (Probe E) (BinaryBase E) Unit (Licence E) (Publication E V) :=
  instrument N.scaled BinaryParity.basis short

noncomputable def nclEndpoint (N : Network E V) (a : E → Bool) (ha : N.Legal a)
    (short : Bool := false) : (nclInstrument N short).State 0 :=
  endpoint BinaryParity.basis a ((N.legal_iff_scaled a).mp ha) N.weights_bound N.capacity_bound

theorem ncl_exactly_one (N : Network E V) {short : Bool} : ∃! g, ((nclInstrument N short).second g).isSome = true :=
  exactly_one N.scaled BinaryParity.basis short

theorem ncl_licence_duration (N : Network E V) (g : Licence E) {short : Bool} :
    ((nclInstrument N short).native.license g).left.length =
      if ((nclInstrument N short).second g).isSome then (if short then 1 else 2) else 3 := by
  rcases g with (u | ⟨i,b⟩) <;> cases short <;> rfl

omit [DecidableEq E] in
theorem ncl_base_size :
    Fintype.card E + 2 ≤ Fintype.card (BinaryBase E) ∧
      Fintype.card (BinaryBase E) < 2 * (Fintype.card E + 2) := by
  simpa only [Probe, Fintype.card_option, Nat.succ_eq_add_one, Nat.add_assoc] using
    (BinaryParity.size_bounds (I := Probe E))

theorem ncl_chain_iff (N : Network E V) {short : Bool} {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b) :
    (nclInstrument N short).Chain (tolerance E V (BinaryBase E))
      (nclEndpoint N a ha short) (nclEndpoint N b hb short) ↔ N.Flips a b :=
  (chain_iff_flips (B := BinaryParity.basis) ((N.legal_iff_scaled a).mp ha)
    ((N.legal_iff_scaled b).mp hb) N.weights_bound N.capacity_bound).trans (N.flips_iff_scaled a b).symm

theorem ncl_fine_iff (N : Network E V) {short : Bool} {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b) :
    (nclInstrument N short).Factorable (nclEndpoint N a ha short) (nclEndpoint N b hb short) ↔ N.Flips a b :=
  (fine_iff_flips (B := BinaryParity.basis) ((N.legal_iff_scaled a).mp ha)
    ((N.legal_iff_scaled b).mp hb) N.weights_bound N.capacity_bound).trans (N.flips_iff_scaled a b).symm

theorem ncl_endpoints_distinct (N : Network E V) {short : Bool} {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b)
    (hab : a ≠ b) : nclEndpoint N a ha short ≠ nclEndpoint N b hb short :=
  endpoints_distinct (B := BinaryParity.basis) ((N.legal_iff_scaled a).mp ha)
    ((N.legal_iff_scaled b).mp hb) N.weights_bound N.capacity_bound hab

/-- The same instrument and licence names, with the additive test replaced by LL ∼ LL. -/
abbrev controlInstrument (G : Graph E V) (B : ParityBasis (Probe E) X) := (instrument G B false).base

omit [DecidableEq V] [DecidableEq X] [Nonempty X] in
theorem control_replacement (G : Graph E V) (B : ParityBasis (Probe E) X) :
    let D := controlInstrument G B
    (D.license (.inl ())).left = [leftMark, leftMark] ∧
    (D.license (.inl ())).right = [leftMark, leftMark] ∧
    ∀ i b, D.license (.inr (i,b)) = (instrument G B false).native.license (.inr (i,b)) := by
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

namespace Control

private abbrev Index (E V : Type*) := Mark E V × Probe E
private abbrev SpectralLegal (G : Graph E V) (B : ParityBasis (Probe E) X) :=
  Legal ((controlInstrument G B).protocol.fiber profile).spectralChecks
    (spectrumBudgets (M := Mark E V) (I := Probe E) (1/2))

private theorem selector_iff (x : Index E V → ℚ) (i : E) (b : Bool) (j : Probe E) :
    (routeCharacterTest (pair G (.inr (i,b))).left (pair G (.inr (i,b))).right j).holds x ↔
      x (selector i,j) * (x (toggle b,j) * x (vertex (G.tail i b),j)) =
        x (selector i,j) * (x (toggle b,j) * x (selector i,j)) := by
  simp [MonomialTest.holds, routeCharacterTest, pair, TimedPair.left, TimedPair.right,
    character_monomial _ _ (fun m j => x (m,j))]

private theorem calibration_iff (x : Index E V → ℚ) (m : Mark E V) (i : Probe E) (c : ℚ) :
    (calibrationTest m i c).holds x ↔ x (m,i) = c := by
  change monomial (pointExponent (m,i)) x = c * monomial (fun _ => 0) x ↔ _
  rw [pointMonomial]
  simp [monomial]

omit [DecidableEq X] [Nonempty X] in
private theorem spectral_iff (x : Index E V → ℚ) :
    SpectralLegal G B x ↔
    (∀ m, (∑ j, |x (m,j)|) ≤ 1/2) ∧
    (∀ e m j c, audit G e = .calibration m j c → x (m,j) = c) ∧
    ∀ i b j, x (selector i,j) * (x (toggle b,j) * x (vertex (G.tail i b),j)) =
      x (selector i,j) * (x (toggle b,j) * x (selector i,j)) := by
  let D := controlInstrument G B
  constructor
  · intro hx
    refine ⟨fun m => spectrum_budget hx m, ?_, ?_⟩
    · intro e m j c he
      apply (calibration_iff x m j c).mp
      apply hx.1
      change calibrationTest m j c ∈ D.protocol.checks.spectralTests Finset.univ Finset.univ
      apply List.mem_append_right
      refine List.mem_flatMap.mpr ⟨e, by simp, ?_⟩
      have he' : D.audit e = .calibration m j c := he
      dsimp only [NativeExperiments.protocol]
      rw [he']
      simp
    · intro i b j
      apply (selector_iff x i b j).mp
      apply hx.1
      change _ ∈ D.protocol.checks.spectralTests Finset.univ Finset.univ
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨.inr (i,b), by simp, List.mem_map_of_mem (by simp)⟩
  · rintro ⟨hbudget, hcalibration, hselector⟩
    refine ⟨fun row hr => ?_, fun budget hb => ?_⟩
    · change row ∈ D.protocol.checks.spectralTests Finset.univ Finset.univ at hr
      simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap] at hr
      rcases hr with (hr | ⟨g, _, hg⟩) | ⟨e, _, he⟩
      · change row ∈ Finset.univ.toList.map (reversalTest (id : Mark E V → Mark E V)) at hr
        obtain ⟨⟨m,i⟩,_,rfl⟩ := List.mem_map.mp hr
        simp [reversalTest, MonomialTest.holds]
      · change row ∈ Finset.univ.toList.map (routeCharacterTest (D.license g).left (D.license g).right) at hg
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
        rcases g with (_ | ⟨i,b⟩)
        · simp [routeCharacterTest, MonomialTest.holds, D, EventExperiments.base,
            EventExperiments.basePair, EventExperiments.reflexivePair, instrument, second,
            pair, TimedPair.left, TimedPair.right]
        · exact (selector_iff x i b j).mpr (hselector i b j)
      · obtain ⟨m,j,c,he',_⟩ := encoded_calibration (G := G) (⟨fun _ _ => 0, fun _ _ => 0⟩ : Graph.Point E V) e
        have ha : D.audit e = .calibration m j c := he'
        dsimp only [NativeExperiments.protocol] at he
        rw [ha] at he
        obtain rfl := List.mem_singleton.mp he
        exact (calibration_iff x m j c).mpr (hcalibration e m j c he')
    · unfold spectrumBudgets at hb
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
      change (∑ i ∈ Finset.univ.map _, |x i|) ≤ 1/2
      rw [Finset.sum_map]
      exact hbudget m

private abbrev summand (m : Mark E V) : Prop := m = toggle false ∨ m = toggle true

omit [Fintype V] [DecidableEq V] in
private theorem audit_not_summand {e : Publication E V} {m : Mark E V} {j : Probe E} {c : ℚ}
    (h : audit G e = .calibration m j c) : ¬ summand m := by
  rcases e with (i | ⟨u,i⟩ | v) <;>
    simp only [audit, AuditQuery.calibration.injEq] at h <;>
    rw [← h.1] <;> simp [summand, leftMark, selector, vertex, toggle]

private def damp (x : Index E V → ℚ) (t : ℚ) (i : Index E V) : ℚ :=
  if summand i.1 then t * x i else x i

omit [DecidableEq X] [Nonempty X] in
private theorem damp_lawful (x : Index E V → ℚ) (hx : SpectralLegal G B x)
    (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1) : SpectralLegal G B (damp x t) := by
  obtain ⟨hbud, hcal, hsel⟩ := (spectral_iff x).mp hx
  apply (spectral_iff (damp x t)).mpr
  refine ⟨fun m => ?_, fun e m j c he => ?_, fun i b j => ?_⟩
  · apply le_trans _ (hbud m)
    apply Finset.sum_le_sum
    intro j _
    by_cases hm : summand m
    · rw [damp, if_pos hm, abs_mul, abs_of_nonneg ht]
      exact mul_le_of_le_one_left (abs_nonneg _) ht'
    · simp [damp, hm]
  · simpa only [damp, if_neg (audit_not_summand he)] using hcal e m j c he
  · have hs : ¬ summand (selector i : Mark E V) := by simp [summand, selector, toggle]
    have hv : ¬ summand (vertex (G.tail i b) : Mark E V) := by simp [summand, vertex, toggle]
    have hb : summand (toggle b : Mark E V) := by cases b <;> simp [summand]
    simp only [damp, if_neg hs, if_neg hv, if_pos hb]
    linear_combination t * hsel i b j

omit [Fintype E] [Fintype V] in
private theorem damp_zero_toggle (x : Index E V → ℚ) (b : Bool) (j : Probe E) :
    damp x 0 (toggle b,j) = 0 := by
  cases b <;> simp [damp, summand]

omit [DecidableEq X] [Nonempty X] in
private theorem mix_damped_lawful (x y : Index E V → ℚ) (hx : SpectralLegal G B (damp x 0))
    (hy : SpectralLegal G B (damp y 0)) (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    SpectralLegal G B (fun i => Graph.mix (damp x 0 i) (damp y 0 i) t) := by
  obtain ⟨hxB, hxC, _⟩ := (spectral_iff _).mp hx
  obtain ⟨hyB, hyC, _⟩ := (spectral_iff _).mp hy
  apply (spectral_iff _).mpr
  refine ⟨fun m => ?_, fun e m j c he => ?_, fun i b j => ?_⟩
  · calc
      _ ≤ ∑ j, Graph.mix |damp x 0 (m,j)| |damp y 0 (m,j)| t := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Graph.mix, abs_mul, abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr ht')]
          using abs_add_le ((1-t) * damp x 0 (m,j)) (t * damp y 0 (m,j))
      _ ≤ 1/2 := by
        simp only [Graph.mix, Finset.sum_add_distrib, ← Finset.mul_sum]
        exact Graph.mix_le (hxB m) (hyB m) ht ht'
  · rw [hxC e m j c he, hyC e m j c he, Graph.mix_self]
  · simp [damp_zero_toggle, Graph.mix_self]

omit [DecidableEq X] [Nonempty X] in
private theorem affine_fine {x y : Index E V → ℚ}
    (hpath : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → SpectralLegal G B (fun i => Graph.mix (x i) (y i) t)) :
    FineConnected ((controlInstrument G B).protocol.fiber profile).spectralChecks
      (spectrumBudgets (1/2)) x y := by
  intro ε hε
  let C : ℚ := 1 + ∑ i, |y i - x i|
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (i : Index E V) : |y i - x i| ≤ C := by
    have h := Finset.single_le_sum (f := fun j => |y j - x j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hmesh := Graph.mesh_of_lipschitz
    (step := LocalStep ((controlInstrument G B).protocol.fiber profile).spectralChecks
      (spectrumBudgets (1/2))) (fun t _ _ i => Graph.mix (x i) (y i) t) hC hε
    (fun s t hs hs' ht ht' hd => ⟨hpath s hs hs', hpath t ht ht', fun i => by
      rw [Graph.mix_dist]
      exact ((mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _))).trans_lt hd⟩)
  simpa [Graph.mix] using hmesh

omit [DecidableEq X] [Nonempty X] in
private theorem damp_fine {x : Index E V → ℚ} (hx : SpectralLegal G B x) :
    FineConnected ((controlInstrument G B).protocol.fiber profile).spectralChecks
      (spectrumBudgets (1/2)) (damp x 0) x := by
  apply affine_fine
  intro t ht ht'
  have he : (fun i => Graph.mix (damp x 0 i) (x i) t) = damp x t := by
    funext i
    by_cases h : summand i.1
    · simp [damp, h, Graph.mix]
    · simp [damp, h, Graph.mix_self]
  rw [he]
  exact damp_lawful x hx t ht ht'

omit [DecidableEq X] [Nonempty X] in
private theorem control_spectra_fine {x y : Index E V → ℚ}
    (hx : SpectralLegal G B x) (hy : SpectralLegal G B y) :
    FineConnected ((controlInstrument G B).protocol.fiber profile).spectralChecks
      (spectrumBudgets (1/2)) x y := by
  refine (damp_fine hx).symm.trans ((affine_fine ?_).trans (damp_fine hy))
  intro t ht ht'
  exact mix_damped_lawful x y (damp_lawful x hx 0 le_rfl zero_le_one)
    (damp_lawful y hy 0 le_rfl zero_le_one) t ht ht'

/-- The endpoint is the unchanged base-protocol state of the original reduction. -/
noncomputable def endpoint (N : Network E V) (a : E → Bool) (ha : N.Legal a) :
    (controlInstrument N.scaled BinaryParity.basis).protocol.State 0 :=
  (nclEndpoint N a ha false).val

theorem endpoint_profile (N : Network E V) (a : E → Bool) (ha : N.Legal a) :
    (endpoint N a ha).profile = profile := rfl

theorem fine (N : Network E V) {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b) :
    (controlInstrument N.scaled BinaryParity.basis).protocol.Factorable
      (endpoint N a ha) (endpoint N b hb) := by
  intro ε hε
  let A := endpoint N a ha
  let C := endpoint N b hb
  let D := (controlInstrument N.scaled BinaryParity.basis).protocol
  let make (u : Index E V → ℚ) := { A.law with spectrum := u }
  let s (u : {u : Index E V → ℚ // SpectralLegal N.scaled BinaryParity.basis u}) : D.State 0 :=
    ⟨profile, make u, ⟨A.legal.1, A.legal.2.1, A.legal.2.2.1, u.2,
      A.legal.2.2.2.2.1, A.legal.2.2.2.2.2⟩⟩
  have hsmall := smallFor_pos (E := E) hε
  have h := control_spectra_fine (B := BinaryParity.basis) A.legal.2.2.2.1 C.legal.2.2.2.1
    (smallFor E ε) hsmall
  have hlift {x y : Index E V → ℚ}
      (h : Relation.ReflTransGen (LocalStep (D.fiber profile).spectralChecks (spectrumBudgets (1/2))
        (smallFor E ε)) x y) (hx : SpectralLegal N.scaled BinaryParity.basis x)
      (hy : SpectralLegal N.scaled BinaryParity.basis y) :
      D.Chain ε (s ⟨x,hx⟩) (s ⟨y,hy⟩) := by
    induction h with
    | refl => exact .refl
    | @tail u v _ hs ih =>
      apply (ih hs.1).tail
      refine ⟨.rewrite, ?_⟩
      simp only [Protocol.Step]
      refine ⟨rfl, ?_⟩
      rintro m ⟨x, ⟨⟩⟩ ⟨y, ⟨⟩⟩
      change |rates m * (BinaryParity.basis (I := Probe E)).kernel (fun j => u (m,j)) x y * 1 -
        rates m * (BinaryParity.basis (I := Probe E)).kernel (fun j => v (m,j)) x y * 1| < ε
      rw [mul_one, mul_one, ← mul_sub, abs_mul, abs_of_nonneg (rates_between m).1]
      have hk := (BinaryParity.basis (I := Probe E)).kernel_sub_le (fun j => (hs.2.2 (m,j)).le) x y
      refine ((mul_le_of_le_one_left (abs_nonneg _) (rates_between m).2).trans hk).trans_lt ?_
      have he : ((Fintype.card (Probe E) : ℚ) + 1) * smallFor E ε = ε := by
        unfold smallFor
        have hn : (Fintype.card (Probe E) : ℚ) + 1 ≠ 0 := by positivity
        field_simp
      linarith
  exact hlift h A.legal.2.2.2.1 C.legal.2.2.2.1

theorem verdict_changes (N : Network E V) {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b)
    (h : ¬ N.Flips a b) :
    ¬ (nclInstrument N false).Factorable (nclEndpoint N a ha false) (nclEndpoint N b hb false) ∧
    (controlInstrument N.scaled BinaryParity.basis).protocol.Factorable (endpoint N a ha) (endpoint N b hb) :=
  ⟨fun h' => h ((ncl_fine_iff N ha hb).mp h'), fine N ha hb⟩

end Control
end MovingProjection.SingleAdditiveLicence
