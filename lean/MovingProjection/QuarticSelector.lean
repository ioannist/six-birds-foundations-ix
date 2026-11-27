import MovingProjection.RationalBridge
import MovingProjection.ResponseBudgets
import MovingProjection.ConstraintLogic

/-! Fixed-variable quartics and the normalized two-face rational selector.
The code checks the arithmetic source construction and the measured
row-to-chain transfer. The fixed-layout assembly of rows is proved in
BoundaryCorollaries.md. -/

namespace MovingProjection.QuarticSelector

open scoped BigOperators

abbrev Power (n : ℕ) := {e : Fin n → Fin 5 // (∑ i, (e i).val) ≤ 4}
abbrev Coeff (n : ℕ) := Power n → ℚ
abbrev Coordinates (n : ℕ) := Fin n ⊕ Fin 4

def degree {n : ℕ} (e : Power n) : ℕ := ∑ i, (e.val i).val

def value {n : ℕ} (c : Coeff n) (v : Fin n → ℚ) : ℚ :=
  ∑ e, c e * ∏ i, v i ^ (e.val i).val

def homogeneous {n : ℕ} (c : Coeff n) (p : Fin n → ℚ) (d : ℚ) : ℚ :=
  ∑ e, c e * (∏ i, p i ^ (e.val i).val) * d ^ (4 - degree e)

def HasRoot {n : ℕ} (c : Coeff n) : Prop := ∃ v, value c v = 0

theorem homogeneous_scale {n : ℕ} (c : Coeff n) (v : Fin n → ℚ) (d : ℚ) :
    homogeneous c (fun i => d * v i) d = d ^ 4 * value c v := by
  unfold homogeneous value
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← degree]
  calc
    _ = d ^ degree e * d ^ (4 - degree e) * (c e * ∏ i, v i ^ (e.val i).val) := by ring
    _ = _ := by
      have he : degree e ≤ 4 := e.property
      rw [← pow_add, Nat.add_sub_of_le he]

theorem homogeneous_div {n : ℕ} (c : Coeff n) (p : Fin n → ℚ) {d : ℚ}
    (h : d ≠ 0) : homogeneous c p d = d ^ 4 * value c (fun i => p i / d) := by
  rw [← homogeneous_scale]
  congr 1
  funext i
  field_simp

def selector {n : ℕ} (x : Coordinates n → ℚ) := x (.inr 0)
def p {n : ℕ} (x : Coordinates n → ℚ) (i : Fin n) := 2 * x (.inl i) - 1
def denom {n : ℕ} (x : Coordinates n → ℚ) := 2 * x (.inr 1)
def radical {n : ℕ} (x : Coordinates n → ℚ) := 1 + 2 * x (.inr 2)
def slack {n : ℕ} (x : Coordinates n → ℚ) := 2 * x (.inr 3) - 1
def gate (s : ℚ) := s * (1 - s)

def InBox {n : ℕ} (x : Coordinates n → ℚ) := ∀ i, 0 ≤ x i ∧ x i ≤ 1

def Lawful {n : ℕ} (c : Coeff n) (x : Coordinates n → ℚ) : Prop :=
  InBox x ∧
    gate (selector x) * homogeneous c (p x) (denom x) = 0 ∧
    gate (selector x) * ((radical x)^2 - (2 + (denom x)^2 * slack x)) = 0

theorem face_lawful {n : ℕ} (c : Coeff n) {x : Coordinates n → ℚ} (hx : InBox x)
    (hs : selector x = 0 ∨ selector x = 1) : Lawful c x := by
  refine ⟨hx, ?_⟩
  rcases hs with h | h <;> norm_num [gate, h]

theorem interior_hasRoot {n : ℕ} {c : Coeff n} {x : Coordinates n → ℚ} (hx : Lawful c x)
    (h0 : selector x ≠ 0) (h1 : selector x ≠ 1) : HasRoot c := by
  have hg : gate (selector x) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr h1.symm)
  have hslack := (mul_eq_zero.mp hx.2.2).resolve_left hg
  have hd : denom x ≠ 0 := by
    intro hh
    have hw : 0 ≤ radical x := by unfold radical; linarith [(hx.1 (.inr 2)).1]
    apply RationalBridge.no_rational_sqrt_two (radical x) hw
    rw [hh] at hslack
    nlinarith
  have hquartic := (mul_eq_zero.mp hx.2.1).resolve_left hg
  rw [homogeneous_div c (p x) hd] at hquartic
  exact ⟨_, (mul_eq_zero.mp hquartic).resolve_left (pow_ne_zero _ hd)⟩

theorem no_root_selector {n : ℕ} {c : Coeff n} (hc : ¬ HasRoot c)
    {x : Coordinates n → ℚ} (hx : Lawful c x) : selector x = 0 ∨ selector x = 1 := by
  by_contra! h
  exact hc (interior_hasRoot hx h.1 h.2)

def endpoint {n : ℕ} (t : ℚ) : Coordinates n → ℚ
  | .inl _ => 0
  | .inr j => if j = 0 then t else 0

theorem endpoint_lawful {n : ℕ} (c : Coeff n) {t : ℚ} (ht : t = 0 ∨ t = 1) :
    Lawful c (endpoint t) := by
  apply face_lawful c
  · rintro (i | j)
    · simp [endpoint]
    · rcases ht with h | h <;> by_cases hj : j = 0 <;> simp [endpoint, h, hj]
  · simpa [selector, endpoint] using ht

def line {n : ℕ} (a b : Coordinates n → ℚ) (t : ℚ) (i : Coordinates n) :=
  (1 - t) * a i + t * b i

private theorem line_in_box {n : ℕ} {a b : Coordinates n → ℚ}
    (ha : InBox a) (hb : InBox b) {t : ℚ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    InBox (line a b t) := by
  intro i
  have h0 := sub_nonneg.mpr ht'
  refine ⟨add_nonneg (mul_nonneg h0 (ha i).1) (mul_nonneg ht (hb i).1), ?_⟩
  have h := add_le_add (mul_le_mul_of_nonneg_left (ha i).2 h0)
    (mul_le_mul_of_nonneg_left (hb i).2 ht)
  simpa [line] using h

/-- All three affine segments of a yes-instance lie in the rational lawful box.
The endpoints of the middle segment are on opposite selector faces. -/
theorem root_has_three_segments {n : ℕ} {c : Coeff n} (hc : HasRoot c) :
    ∃ a b : Coordinates n → ℚ, selector a = 0 ∧ selector b = 1 ∧
      ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
        Lawful c (line (endpoint 0) a t) ∧ Lawful c (line a b t) ∧
          Lawful c (line b (endpoint 1) t) := by
  obtain ⟨v, hv⟩ := hc
  let S := ∑ i, |v i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let d := 1 / (1 + S)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : d ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  obtain ⟨w, u, hw, hw', hu, hwu⟩ := RationalBridge.exists_bounded_slack hd hd'
  let point (t : ℚ) : Coordinates n → ℚ
    | .inl i => (d * v i + 1) / 2
    | .inr j =>
      if j = 0 then t else if j = 1 then d / 2 else if j = 2 then (w - 1) / 2 else (u + 1) / 2
  have hpoint (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1) : InBox (point t) := by
    rintro (i | j)
    · have hi : |v i| ≤ S :=
        Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
      have h : |d * v i| ≤ 1 := by
        rw [abs_mul, abs_of_pos hd]
        dsimp [d]
        rw [div_mul_eq_mul_div, one_mul]
        exact (div_le_one (by positivity)).mpr (by linarith)
      obtain ⟨hl, hr⟩ := abs_le.mp h
      change 0 ≤ (d * v i + 1) / 2 ∧ (d * v i + 1) / 2 ≤ 1
      constructor <;> linarith
    · fin_cases j
      all_goals simp [point, ht, ht'] <;>
        constructor <;> linarith [hd.le, hd', hw, hw', (abs_le.mp hu).1, (abs_le.mp hu).2]
  have hmiddle (t : ℚ) (ht : 0 ≤ t) (ht' : t ≤ 1) : Lawful c (point t) := by
    have hp : p (point t) = fun i => d * v i := by funext i; simp [p, point]; ring
    have hdval : denom (point t) = d := by simp [denom, point]; ring
    have hwval : radical (point t) = w := by simp [radical, point]; ring
    have huval : slack (point t) = u := by simp [slack, point]; ring
    refine ⟨hpoint t ht ht', ?_, ?_⟩
    · rw [hp, hdval, homogeneous_scale, hv, mul_zero, mul_zero]
    · rw [hdval, hwval, huval, hwu, sub_self, mul_zero]
  have hline (t : ℚ) : line (point 0) (point 1) t = point t := by
    funext i
    rcases i with i | j
    · simp only [line, point]; ring
    · by_cases hj : j = 0 <;> simp only [line, point, hj, if_true, if_false] <;> ring
  have hl (t : ℚ) : selector (line (endpoint 0) (point 0) t) = 0 := by
    simp [selector, line, endpoint, point]
  have hr (t : ℚ) : selector (line (point 1) (endpoint 1) t) = 1 := by
    simp [selector, line, endpoint, point]
  refine ⟨point 0, point 1, rfl, rfl, fun t ht ht' => ⟨?_, ?_, ?_⟩⟩
  · exact face_lawful c (line_in_box (endpoint_lawful c (.inl rfl)).1
      (hpoint 0 le_rfl zero_le_one) ht ht') (.inl (hl t))
  · rw [hline]
    exact hmiddle t ht ht'
  · exact face_lawful c (line_in_box (hpoint 1 zero_le_one le_rfl)
      (endpoint_lawful c (.inr rfl)).1 ht ht') (.inr (hr t))

open ResponseBudgets CalibratedResponses

set_option synthInstance.maxSize 512
attribute [local instance] ResponseBudgets.auxDecidableEq

variable {n : ℕ} {J T X : Type*} [Fintype J] [Fintype T] [Fintype X]
  [DecidableEq J] [DecidableEq T] [DecidableEq X] [Nonempty X]

/-- The fixed-layout compiler supplies this bridge. The coordinate lift has
bounded slopes on each affine segment of the source box. -/
structure RowRealization (c : Coeff n) (P : Rows J T) where
  coordinate : Coordinates n → J
  lift : (Coordinates n → ℚ) → J → ℚ
  lift_coordinate : ∀ x i, lift x (coordinate i) = x i
  lift_lawful : ∀ x, Lawful c x → Solution P (lift x)
  read_lawful : ∀ y, Solution P y → Lawful c (y ∘ coordinate)
  slope : ℚ
  slope_pos : 0 < slope
  lift_near : ∀ a b, InBox a → InBox b → ∀ s t : ℚ,
    0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      ∀ j, |lift (line a b s) j - lift (line a b t) j| ≤ slope * |s - t|

namespace RowRealization

variable {c : Coeff n} {P : Rows J T} (F : RowRealization c P)

omit [Fintype T] [DecidableEq T] in
private theorem lifted_segment {a b : Coordinates n → ℚ}
    (hline : ∀ t : ℚ, 0 ≤ t → t ≤ 1 → Lawful c (line a b t))
    {ε : ℚ} (hε : 0 < ε) :
    BoxChain (P := P) ε (F.lift a) (F.lift b) := by
  have h0 : line a b 0 = a := by funext i; simp [line]
  have h1 : line a b 1 = b := by funext i; simp [line]
  have ha : Lawful c a := h0 ▸ hline 0 le_rfl zero_le_one
  have hb : Lawful c b := h1 ▸ hline 1 zero_le_one le_rfl
  have hp := ConstraintLogic.Graph.mesh_of_lipschitz (step := BoxStep (P := P))
    (fun t _ _ => F.lift (line a b t)) F.slope_pos hε
    (fun s t hs hs' ht ht' hd =>
      ⟨F.lift_lawful _ (hline s hs hs'), F.lift_lawful _ (hline t ht ht'),
        fun j => (F.lift_near a b ha.1 hb.1 s t hs hs' ht ht' j).trans_lt hd⟩)
  simpa only [h0, h1] using hp

omit [Fintype T] [DecidableEq T] in
theorem row_fine_of_root (h : HasRoot c) {ε : ℚ} (hε : 0 < ε) :
    BoxChain (P := P) ε (F.lift (endpoint 0)) (F.lift (endpoint 1)) := by
  obtain ⟨a,b,_,_,hseg⟩ := root_has_three_segments h
  exact (F.lifted_segment (fun t ht ht' => (hseg t ht ht').1) hε).trans
    ((F.lifted_segment (fun t ht ht' => (hseg t ht ht').2.1) hε).trans
      (F.lifted_segment (fun t ht ht' => (hseg t ht ht').2.2) hε))

omit [Fintype T] [DecidableEq T] in
theorem row_selector_of_no_root (hc : ¬ HasRoot c) (x : J → ℚ) (hx : Solution P x) :
    x (F.coordinate (.inr 0)) = 0 ∨ x (F.coordinate (.inr 0)) = 1 :=
  no_root_selector hc (F.read_lawful x hx)

noncomputable def nativeEndpoint (B : ParityBasis (Probe J) X) (t : ℚ)
    (ht : t = 0 ∨ t = 1) : Native P B :=
  ResponseBudgets.lift B (F.lift (endpoint t)) (F.lift_lawful _ (endpoint_lawful c ht))

theorem nativeEndpoints_distinct (B : ParityBasis (Probe J) X) :
    F.nativeEndpoint B 0 (.inl rfl) ≠ F.nativeEndpoint B 1 (.inr rfl) := by
  intro h
  have h' := congrArg (fun a : Native P B => decode a (F.coordinate (.inr 0))) h
  simp [nativeEndpoint, decode_lift, F.lift_coordinate, endpoint] at h'

theorem native_boundary (B : ParityBasis (Probe J) X) :
    let a := F.nativeEndpoint B 0 (.inl rfl)
    let b := F.nativeEndpoint B 1 (.inr rfl)
    let D := instrument (catalogue P) B
    (D.Factorable a b ↔ HasRoot c) ∧
      (D.Chain (nativeMesh J T X 1) a b ↔ HasRoot c) ∧
      (∃! g, (D.second g).isSome = true) := by
  dsimp only
  have hmesh : 0 < nativeMesh J T X 1 := by
    unfold nativeMesh
    have := CalibratedResponses.floor_pos (M := Aux J T)
    have := ResponseBudgets.amplitude_pos (J := J)
    positivity
  have hyes (h : HasRoot c) :
      (instrument (catalogue P) B).Factorable
        (F.nativeEndpoint B 0 (.inl rfl)) (F.nativeEndpoint B 1 (.inr rfl)) :=
    (fine_iff_box _ _).mpr (fun _ hε => F.row_fine_of_root h hε)
  have hno (h : ¬ HasRoot c) :
      ¬ (instrument (catalogue P) B).Chain (nativeMesh J T X 1)
        (F.nativeEndpoint B 0 (.inl rfl)) (F.nativeEndpoint B 1 (.inr rfl)) := by
    apply no_native_chain_of_selector _ _ (F.coordinate (.inr 0))
    · simp [F.lift_coordinate, endpoint]
    · simp [F.lift_coordinate, endpoint]
    · exact F.row_selector_of_no_root h
  have hchain :
      (instrument (catalogue P) B).Chain (nativeMesh J T X 1)
        (F.nativeEndpoint B 0 (.inl rfl)) (F.nativeEndpoint B 1 (.inr rfl)) ↔ HasRoot c :=
    ⟨fun h => by by_contra hn; exact hno hn h, fun h => hyes h _ hmesh⟩
  exact ⟨⟨fun h => hchain.mp (h _ hmesh), hyes⟩, hchain, exactly_one (catalogue P) B⟩

end RowRealization
end MovingProjection.QuarticSelector
