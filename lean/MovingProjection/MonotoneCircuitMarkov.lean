import MovingProjection.NativeCoreOrder
import MovingProjection.CommitLateExample
import Mathlib.Tactic.DeriveFintype

/-! Monotone circuit evaluation as fine reachability with single-word licences. -/

namespace MovingProjection.MonotoneCircuitMarkov

open scoped BigOperators

inductive Gate (V : Type) where
  | const (value : Bool)
  | conj (a b : V)
  | disj (a b : V)
  deriving DecidableEq

def Gate.inputs {V : Type} : Gate V → List V
  | .const _ => []
  | .conj a b | .disj a b => [a,b]

structure Circuit (n : ℕ) where
  gate : Fin n → Gate (Fin n)
  earlier : ∀ i j, j ∈ (gate i).inputs → j < i
  out : Fin n

variable {n : ℕ}

set_option linter.unusedVariables false in
def Circuit.value (C : Circuit n) (i : Fin n) : Bool :=
  match h : C.gate i with
  | .const v => v
  | .conj a b => C.value a && C.value b
  | .disj a b => C.value a || C.value b
termination_by i.val
decreasing_by all_goals exact C.earlier i _ (by simp [h,Gate.inputs])

theorem Circuit.value_const (C : Circuit n) {i : Fin n} {v : Bool}
    (h : C.gate i = .const v) : C.value i = v := by
  rw [Circuit.value,h]

theorem Circuit.value_conj (C : Circuit n) {i a b : Fin n}
    (h : C.gate i = .conj a b) : C.value i = (C.value a && C.value b) := by
  rw [Circuit.value,h]

theorem Circuit.value_disj (C : Circuit n) {i a b : Fin n}
    (h : C.gate i = .disj a b) : C.value i = (C.value a || C.value b) := by
  rw [Circuit.value,h]

inductive Mark (n : ℕ) where
  | anchor
  | sentinel
  | wire (i : Fin n)
  deriving DecidableEq, Fintype

def markEquiv (n : ℕ) : Mark n ≃ Unit ⊕ (Unit ⊕ Fin n) where
  toFun
    | .anchor => .inl ()
    | .sentinel => .inr (.inl ())
    | .wire i => .inr (.inr i)
  invFun
    | .inl _ => .anchor
    | .inr (.inl _) => .sentinel
    | .inr (.inr i) => .wire i
  left_inv := by intro m; cases m <;> rfl
  right_inv := by rintro (⟨⟩ | (⟨⟩ | i)) <;> rfl
abbrev Index (n : ℕ) := Mark n × Unit
abbrev Licence (n : ℕ) := Unit ⊕ (Fin n × Bool)

abbrev anchor : Mark n := .anchor
abbrev sentinel : Mark n := .sentinel
abbrev wire (i : Fin n) : Mark n := .wire i

instance : Nonempty (Mark n) := ⟨anchor⟩

@[simp] theorem anchor_ne_sentinel : (anchor : Mark n) ≠ sentinel := by
  intro h
  cases h

@[simp] theorem wire_ne_sentinel (i : Fin n) : wire i ≠ sentinel := by
  intro h
  cases h

def coord (m : Mark n) : Index n := (m, ())

namespace Circuit

variable (C : Circuit n)

def gateHead (i : Fin n) : Mark n :=
  match C.gate i with
  | .const true => anchor
  | _ => wire i

def guards (i : Fin n) (slot : Bool) : Mark n × Mark n :=
  match C.gate i with
  | .const _ => (anchor,anchor)
  | .conj a b => (wire (if slot then b else a),anchor)
  | .disj a b => (wire a,wire b)

def gatePair (i : Fin n) (slot : Bool) : TimedPair (Mark n) 3 :=
  let g := C.guards i slot
  ⟨C.gateHead i, anchor, [g.1,g.2], [g.1,g.2], rfl, le_rfl⟩

def outputPair : TimedPair (Mark n) 3 :=
  ⟨sentinel,anchor,[sentinel,wire C.out],[anchor,wire C.out],rfl,le_rfl⟩

def pair : Licence n → TimedPair (Mark n) 3
  | .inl _ => C.outputPair
  | .inr (i,slot) => C.gatePair i slot

theorem licence_duration_three (g : Licence n) :
    (C.pair g).left.length = 3 ∧ (C.pair g).right.length = 3 := by
  cases g <;> exact ⟨rfl,rfl⟩

def rate (n : ℕ) : ℚ := 1 / (n + 2 : ℚ)

def instrument : NativeExperiments (Mark n) Unit Bool Unit (Licence n) Unit where
  parity := CommitLateExample.parity
  weights := fun _ => 1
  weights_pos := fun _ => by norm_num
  weights_unit := by simp
  reversal := id
  reversal_involutive := fun _ => rfl
  δ := rate n
  δ_pos := by unfold rate; positivity
  κ := 1/2
  κ_lt_one := by norm_num
  horizon := 3
  license := C.pair
  audit := fun _ => .calibration anchor () (1/4)
  policy := fun held => held = Finset.univ

noncomputable abbrev D := C.instrument.protocol
abbrev State := C.D.State 0

def profile : Capabilities (Mark n) Bool Unit (Licence n) Unit 0 :=
  ⟨OrderDual.toDual Set.univ, fun _ => OrderDual.toDual ⊤, Finset.univ, Finset.univ⟩

def spectrum (negative : Bool) (j : Index n) : ℚ :=
  if negative && decide (j.1 = sentinel) then -1/4 else 1/4

def endpointLaw (n : ℕ) (negative : Bool) : PhysicalLaw (Mark n) Unit Bool Unit :=
  ⟨fun _ => rate n, spectrum negative, fun _ _ _ _ _ => 1⟩

private theorem word_rate (p : TimedPair (Mark n) 3) :
    p.left.length = p.right.length →
    (p.left.map (fun _ => rate n)).prod = (p.right.map (fun _ => rate n)).prod := by
  intro h
  simp [h]

private theorem gateHead_ne_sentinel (i : Fin n) : C.gateHead i ≠ sentinel := by
  cases h : C.gate i with
  | const b => cases b <;> simp [gateHead,h]
  | conj | disj => simp [gateHead,h]

private theorem word_spectrum (negative : Bool) (g : Licence n) :
    ((C.pair g).left.map (fun m => spectrum negative (coord m))).prod =
    ((C.pair g).right.map (fun m => spectrum negative (coord m))).prod := by
  rcases g with (_ | ⟨i,s⟩)
  · cases negative <;> norm_num [pair,outputPair,TimedPair.left,TimedPair.right,spectrum,coord]
  · simp [pair,gatePair,TimedPair.left,TimedPair.right,spectrum,coord,C.gateHead_ne_sentinel]

private theorem endpoint_legal (negative : Bool) : C.D.legal profile (endpointLaw n negative) := by
  refine ⟨fun _ _ _ => le_rfl,rfl,⟨?_,?_,?_,?_⟩⟩
  · refine ⟨fun _ => le_rfl, ?_, ?_⟩
    · have hc : (Fintype.card (Mark n) : ℚ) = n + 2 := by
        rw [Fintype.card_congr (markEquiv n)]
        simp [Fintype.card_sum, add_comm, add_left_comm]
      simp [endpointLaw, rate, hc, show (n + 2 : ℚ) ≠ 0 by positivity]
    · intro t ht
      change t ∈ C.D.checks.rateTests Finset.univ Finset.univ at ht
      simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at ht
      rcases ht with ⟨g,_,hg⟩ | ⟨e,_,he⟩
      · change t ∈ [⟨routeRateRow (C.pair g).left (C.pair g).right,1⟩] at hg
        obtain rfl := List.mem_singleton.mp hg
        apply (route_rate_compile _ _ _ _).2
        simpa [endpointLaw] using word_rate (C.pair g) (C.instrument.licensed_duration g)
      · cases he
  · refine ⟨?_,?_⟩
    · intro t ht
      change t ∈ C.D.checks.spectralTests Finset.univ Finset.univ at ht
      simp only [ProbeCatalog.spectralTests,List.mem_append,List.mem_flatMap] at ht
      rcases ht with (hr | ⟨g,_,hg⟩) | ⟨e,_,he⟩
      · change t ∈ Finset.univ.toList.map (reversalTest id) at hr
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
        simp [MonomialTest.holds,reversalTest]
      · change t ∈ Finset.univ.toList.map
          (routeCharacterTest (C.pair g).left (C.pair g).right) at hg
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
        cases i
        change monomial (characterExponent (C.pair g).left ()) (spectrum negative) =
          1 * monomial (characterExponent (C.pair g).right ()) (spectrum negative)
        simp only [one_mul]
        exact (character_monomial (C.pair g).left () (fun m i => spectrum negative (m,i))).trans
          ((C.word_spectrum negative g).trans
            (character_monomial (C.pair g).right () (fun m i => spectrum negative (m,i))).symm)
      · change t ∈ [calibrationTest anchor () (1/4)] at he
        obtain rfl := List.mem_singleton.mp he
        change monomial (pointExponent (coord anchor)) (spectrum negative) =
          1/4 * monomial (fun _ => 0) (spectrum negative)
        rw [pointMonomial]
        norm_num [monomial,spectrum,coord]
    · intro b hb
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hb
      change (∑ i : Unit, |spectrum negative (m,i)|) ≤ (1/2 : ℚ)
      simp only [Fintype.sum_unique, spectrum]
      split <;> norm_num
  · refine ⟨?_,?_,?_,?_,?_⟩
    all_goals simp [instrument, NativeExperiments.protocol, endpointLaw]
  · ext e
    simp [registerMask, Protocol.fiber, profile, endpointLaw]

def endpoint (negative : Bool) : C.State :=
  ⟨profile,endpointLaw n negative,C.endpoint_legal negative⟩

noncomputable abbrev rows := C.D.spectralRows (profile (n := n))

private abbrev row (p : TimedPair (Mark n) 3) : ExponentRow (Index n) :=
  (routeCharacterTest p.left p.right ()).row

private theorem licence_row (g : Licence n) : row (C.pair g) ∈ C.rows := by
  apply List.mem_map_of_mem
  change routeCharacterTest (C.pair g).left (C.pair g).right () ∈
    C.D.checks.spectralTests Finset.univ Finset.univ
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨g,by simp,List.mem_map_of_mem (by simp)⟩))

private theorem calibration_row :
    (calibrationTest (anchor : Mark n) () (1/4)).row ∈ C.rows := by
  apply List.mem_map_of_mem
  change calibrationTest anchor () (1/4) ∈ C.D.checks.spectralTests Finset.univ Finset.univ
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(),by simp,by simp [instrument,NativeExperiments.protocol]⟩)

private theorem row_cases {r : ExponentRow (Index n)} (hr : r ∈ C.rows) :
    (∃ j, r = (reversalTest id j).row) ∨
      (∃ g, r = row (C.pair g)) ∨ r = (calibrationTest anchor () (1/4)).row := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  change t ∈ C.D.checks.spectralTests Finset.univ Finset.univ at ht
  simp only [ProbeCatalog.spectralTests,List.mem_append,List.mem_flatMap] at ht
  rcases ht with (h | ⟨g,_,h⟩) | ⟨e,_,h⟩
  · change t ∈ Finset.univ.toList.map (reversalTest id) at h
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨j,rfl⟩
  · change t ∈ Finset.univ.toList.map
      (routeCharacterTest (C.pair g).left (C.pair g).right) at h
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    cases i
    exact Or.inr (Or.inl ⟨g,rfl⟩)
  · change t ∈ [calibrationTest anchor () (1/4)] at h
    obtain rfl := List.mem_singleton.mp h
    exact Or.inr (Or.inr rfl)

private theorem active_iff (p : TimedPair (Mark n) 3) (S : Finset (Index n)) :
    (row p).active S ↔
      (∀ m ∈ p.left, coord m ∈ S) ∧ (∀ m ∈ p.right, coord m ∈ S) := by
  constructor
  · intro h
    constructor
    · intro m hm
      by_contra hn
      have he : p.left.count m = 0 := (h (coord m) hn).1
      exact (List.count_eq_zero.mp he) hm
    · intro m hm
      by_contra hn
      have he : p.right.count m = 0 := (h (coord m) hn).2
      exact (List.count_eq_zero.mp he) hm
  · rintro ⟨hl,hr⟩ ⟨m,⟨⟩⟩ hm
    exact ⟨List.count_eq_zero.mpr fun h => hm (hl m h),
      List.count_eq_zero.mpr fun h => hm (hr m h)⟩

private theorem word_weight (w : List (Mark n)) (v : Index n → ℕ) :
    (∑ j, characterExponent w () j * v j) = (w.map (fun m => v (coord m))).sum := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ x, w.count x * v (x,())) = (w.map (fun m => v (m,()))).sum
  induction w with
  | nil => simp
  | cons m w ih =>
    have h (k : Mark n) : (m :: w).count k = w.count k + (if k = m then 1 else 0) := by
      by_cases he : k = m
      · subst k; simp
      · simp [he,Ne.symm he]
    simp only [h, add_mul, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega

private theorem gate_balance (i : Fin n) (s : Bool) (v : Index n → ℕ) :
    (∑ j, (row (C.gatePair i s)).lhs j * v j) =
      (∑ j, (row (C.gatePair i s)).rhs j * v j) ↔
    v (coord (C.gateHead i)) = v (coord anchor) := by
  change (∑ j, characterExponent (C.gatePair i s).left () j * v j) =
      (∑ j, characterExponent (C.gatePair i s).right () j * v j) ↔ _
  rw [word_weight,word_weight]
  simp [gatePair, TimedPair.left, TimedPair.right]

private theorem output_balance (v : Index n → ℕ) :
    (∑ j, (row C.outputPair).lhs j * v j) = (∑ j, (row C.outputPair).rhs j * v j) ↔
      v (coord sentinel) = v (coord anchor) := by
  change (∑ j, characterExponent C.outputPair.left () j * v j) =
    (∑ j, characterExponent C.outputPair.right () j * v j) ↔ _
  rw [word_weight,word_weight]
  simp only [outputPair,TimedPair.left,TimedPair.right,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero]
  omega

private theorem anchor_weight {S : Finset (Index n)} {v : Index n → ℕ}
    (hv : Damping C.rows S v) (hs : coord anchor ∈ S) : v (coord anchor) = 0 := by
  have h : (calibrationTest (anchor : Mark n) () (1/4)).row.active S := by
    intro j hj
    have hn : j ≠ coord anchor := fun h => hj (h.symm ▸ hs)
    simp [calibrationTest,pointExponent,show j ≠ ((anchor : Mark n),()) from hn]
  simpa [calibrationTest,pointExponent,coord] using hv.2 _ C.calibration_row h

def survives : Mark n → Bool
  | .anchor => true
  | .sentinel => !C.value C.out
  | .wire i => !C.value i

def survivors : Finset (Index n) := Finset.univ.filter fun j => C.survives j.1 = true

@[simp] theorem anchor_survives : coord anchor ∈ C.survivors := by
  simp [survivors,survives,coord,anchor]

@[simp] theorem wire_survives (i : Fin n) :
    coord (wire i) ∈ C.survivors ↔ C.value i = false := by
  simp [survivors,survives,coord,wire]

@[simp] theorem sentinel_survives :
    coord sentinel ∈ C.survivors ↔ C.value C.out = false := by
  simp [survivors,survives,coord,sentinel]

private theorem false_gate_guard (i : Fin n) (hi : C.value i = false) :
    ∃ s : Bool, C.gateHead i = wire i ∧
      coord (C.guards i s).1 ∈ C.survivors ∧ coord (C.guards i s).2 ∈ C.survivors := by
  cases e : C.gate i with
  | const b =>
    rw [C.value_const e] at hi
    subst b
    exact ⟨false,by simp [gateHead,e],by simp [guards,e],by simp [guards,e]⟩
  | conj a b =>
    rw [C.value_conj e, Bool.and_eq_false_iff] at hi
    rcases hi with ha | hb
    · exact ⟨false,by simp [gateHead,e],by simpa [guards,e] using ha,by simp [guards,e]⟩
    · exact ⟨true,by simp [gateHead,e],by simpa [guards,e] using hb,by simp [guards,e]⟩
  | disj a b =>
    rw [C.value_disj e, Bool.or_eq_false_iff] at hi
    exact ⟨false,by simp [gateHead,e],by simpa [guards,e] using hi.1,
      by simpa [guards,e] using hi.2⟩

private theorem survivors_irreducible : IrreducibleSupport C.rows C.survivors := by
  apply (irreducibleSupport_iff_core_eq _ _).2
  apply core_eq_self_of_damping_zero
  intro v hv j hj
  have hz := C.anchor_weight hv C.anchor_survives
  have pin (p : TimedPair (Mark n) 3) (hmem : row p ∈ C.rows)
      (hl : ∀ m ∈ p.left, coord m ∈ C.survivors)
      (hr : ∀ m ∈ p.right, coord m ∈ C.survivors) :=
    hv.2 _ hmem ((active_iff p _).2 ⟨hl,hr⟩)
  obtain ⟨m,⟨⟩⟩ := j
  cases m with
  | anchor => exact hz
  | sentinel =>
    have ho : coord (wire C.out) ∈ C.survivors :=
      (C.wire_survives _).2 (C.sentinel_survives.1 hj)
    have h := pin C.outputPair (C.licence_row (.inl ())) (by
      intro k hk
      simp [outputPair,TimedPair.left] at hk
      rcases hk with rfl | rfl
      · exact hj
      · exact ho) (by
      intro k hk
      simp [outputPair,TimedPair.right] at hk
      rcases hk with rfl | rfl
      · exact C.anchor_survives
      · exact ho)
    exact ((C.output_balance v).1 h).trans hz
  | wire i =>
    obtain ⟨s,head,ha,hb⟩ := C.false_gate_guard i ((C.wire_survives i).1 hj)
    have h := pin (C.gatePair i s) (C.licence_row (.inr (i,s))) (by
      intro k hk
      simp [gatePair,TimedPair.left,head] at hk
      rcases hk with rfl | rfl | rfl
      · exact hj
      · exact ha
      · exact hb) (by
      intro k hk
      simp [gatePair,TimedPair.right] at hk
      rcases hk with rfl | rfl | rfl
      · exact C.anchor_survives
      · exact ha
      · exact hb)
    have hh := (C.gate_balance i s v).1 h
    rw [head,hz] at hh
    exact hh

noncomputable abbrev remaining : Finset (Index n) := core C.rows Finset.univ

private theorem gate_guards_of_active (i : Fin n) (slot : Bool) {S : Finset (Index n)}
    (h : (row (C.gatePair i slot)).active S) :
    coord (C.guards i slot).1 ∈ S ∧ coord (C.guards i slot).2 ∈ S := by
  have hl := ((active_iff _ _).1 h).1
  exact ⟨hl _ (by simp [gatePair,TimedPair.left]), hl _ (by simp [gatePair,TimedPair.left])⟩

private theorem gateHead_cases (i : Fin n) :
    C.gateHead i = anchor ∨ C.gateHead i = wire i := by
  cases h : C.gate i with
  | const b => cases b <;> simp [gateHead,h]
  | conj | disj => simp [gateHead,h]

/-- A coordinate whose own pinning rows are all inactive cannot be in the
terminal support. Occurrences in common factors cancel in the weight sums. -/
private theorem cannot_delete {m : Mark n} (hm : m ≠ anchor) (hs : coord m ∈ C.remaining)
    (hgate : ∀ i s, (row (C.gatePair i s)).active C.remaining → C.gateHead i ≠ m)
    (hout : (row C.outputPair).active C.remaining → sentinel ≠ m) : False := by
  let v := pointExponent (coord m)
  have hv : Damping C.rows C.remaining v := by
    refine ⟨fun j hj => ?_, fun r hr ha => ?_⟩
    · have he : j ≠ coord m := fun h => hj (h.symm ▸ hs)
      simp [v,pointExponent,he]
    · rcases C.row_cases hr with ⟨j,rfl⟩ | ⟨g,rfl⟩ | rfl
      · rfl
      · rcases g with (_ | ⟨i,s⟩)
        · change (∑ j, (row C.outputPair).lhs j * v j) =
            ∑ j, (row C.outputPair).rhs j * v j
          apply (C.output_balance v).2
          simp [v,pointExponent,coord,hout ha,Ne.symm hm]
        · change (∑ j, (row (C.gatePair i s)).lhs j * v j) =
            ∑ j, (row (C.gatePair i s)).rhs j * v j
          exact (C.gate_balance i s v).2 (by
            simp [v,pointExponent,coord,hgate i s ha,Ne.symm hm])
      · simp [calibrationTest,pointExponent,v,coord,hm]
  have hfixed : IrreducibleSupport C.rows C.remaining :=
    (irreducibleSupport_iff_core_eq _ _).2 (core_idempotent _ _)
  have he := hfixed _ ⟨v,hv,rfl⟩
  have hmem : coord m ∈ C.remaining.filter (fun j => v j = 0) := he.symm ▸ hs
  have h := (Finset.mem_filter.mp hmem).2
  simp [v,pointExponent] at h

theorem true_wire_absent (i : Fin n) (htrue : C.value i = true) :
    coord (wire i) ∉ C.remaining := by
  induction i using (wellFounded_lt (α := Fin n)).induction with
  | h i ih =>
    intro hi
    apply C.cannot_delete (m := wire i) (by simp [wire,anchor]) hi
    · intro j s ha
      rcases C.gateHead_cases j with hhead | hhead
      · rw [hhead]
        simp [anchor,wire]
      · rw [hhead]
        intro heq
        have he : j = i := by simpa [wire] using heq
        subst j
        have hg := C.gate_guards_of_active i s ha
        have earlier (k : Fin n) (hk : k ∈ (C.gate i).inputs) (hv : C.value k = true) :
            coord (wire k) ∉ C.remaining := ih k (C.earlier i k hk) hv
        cases e : C.gate i with
        | const b =>
          have hv := (C.value_const e).symm.trans htrue
          subst b
          simp [gateHead,e,anchor,wire] at hhead
        | conj a b =>
          have hv : C.value a = true ∧ C.value b = true := by
            simpa only [C.value_conj e,Bool.and_eq_true] using htrue
          cases s
          · exact (earlier a (by simp [e,Gate.inputs]) hv.1) (by simpa [guards,e] using hg.1)
          · exact (earlier b (by simp [e,Gate.inputs]) hv.2) (by simpa [guards,e] using hg.1)
        | disj a b =>
          have hv : C.value a = true ∨ C.value b = true := by
            simpa only [C.value_disj e,Bool.or_eq_true] using htrue
          rcases hv with hv | hv
          · exact (earlier a (by simp [e,Gate.inputs]) hv) (by simpa [guards,e] using hg.1)
          · exact (earlier b (by simp [e,Gate.inputs]) hv) (by simpa [guards,e] using hg.2)
    · intro _
      simp [sentinel,wire]

theorem true_output_sentinel_absent (htrue : C.value C.out = true) :
    coord (sentinel : Mark n) ∉ C.remaining := by
  intro hs
  apply C.cannot_delete (m := sentinel) (by simp [sentinel,anchor]) hs
  · intro i s _
    rcases C.gateHead_cases i with h | h <;> rw [h] <;> simp [sentinel,anchor,wire]
  · intro ha
    have hmem := ((active_iff _ _).1 ha).1 (wire C.out) (by simp [outputPair,TimedPair.left])
    exact (C.true_wire_absent _ htrue hmem).elim

/-- The full-support core retains the anchor, exactly the false gates, and
the sentinel precisely when the distinguished output is false. -/
theorem remaining_eq_survivors : C.remaining = C.survivors := by
  apply Finset.Subset.antisymm _ (C.survivors_irreducible.subset_core (Finset.subset_univ _))
  intro j hj
  obtain ⟨m,⟨⟩⟩ := j
  cases m with
  | anchor => exact C.anchor_survives
  | sentinel =>
    apply C.sentinel_survives.2
    cases h : C.value C.out
    · rfl
    · exact (C.true_output_sentinel_absent h hj).elim
  | wire i =>
    apply (C.wire_survives i).2
    cases h : C.value i
    · rfl
    · exact (C.true_wire_absent i h hj).elim

private theorem endpoint_sign_support (negative : Bool) :
    codeSupport (signCode (embed (spectrum (n := n) negative))) = Finset.univ := by
  rw [codeSupport_signCode, show realSupport (embed (spectrum (n := n) negative)) =
    support (spectrum negative) from realSupport_cast _]
  ext j
  rw [mem_support]
  simp only [Finset.mem_univ,iff_true,spectrum]
  split <;> norm_num

private theorem signature_of_endpoint (negative : Bool) (j : Index n) :
    C.D.signature profile (C.endpoint negative).law j =
      if j ∈ C.survivors then signCode (embed (spectrum negative)) j else 0 := by
  change signedCore C.rows (signCode (embed (spectrum negative))) j = _
  simp only [signedCore,endpoint_sign_support,C.remaining_eq_survivors]

/-- The native endpoints are supplied directly, with no circuit evaluation
in their construction. Their fine reachability is exactly output truth. -/
theorem native_fine_iff_value :
    C.D.Factorable (C.endpoint false) (C.endpoint true) ↔ C.value C.out = true := by
  rw [C.instrument.exact_six_iff]
  change (profile (n := n) ≤ profile ∧
    C.D.signature profile (C.endpoint false).law = C.D.signature profile (C.endpoint true).law) ↔ _
  simp only [le_rfl,true_and]
  constructor
  · intro he
    have h := congrFun he (coord sentinel)
    cases hv : C.value C.out
    · have hm := C.sentinel_survives.2 hv
      simp only [C.signature_of_endpoint, hm, if_true] at h
      have hp : signCode (embed (spectrum (n := n) false)) (coord sentinel) = 1 := by
        apply sign_pos
        norm_num [embed,spectrum]
      have hn : signCode (embed (spectrum (n := n) true)) (coord sentinel) = -1 := by
        apply sign_neg
        norm_num [embed,spectrum,coord]
      rw [hp,hn] at h
      exact ((by decide : (1 : SignType) ≠ -1) h).elim
    · rfl
  · intro hv
    funext j
    rw [C.signature_of_endpoint,C.signature_of_endpoint]
    by_cases hj : j ∈ C.survivors
    · rcases j with ⟨m,⟨⟩⟩
      have hn : m ≠ sentinel := by
        intro he
        subst m
        exact Bool.noConfusion (hv.symm.trans (C.sentinel_survives.1 hj))
      simp [hj,signCode,embed,spectrum,hn]
    · simp [hj]

theorem endpoints_distinct : C.endpoint false ≠ C.endpoint true := by
  intro he
  have h := congrArg (fun a : C.State => a.law.spectrum (coord sentinel)) he
  norm_num [endpoint,endpointLaw,spectrum,coord] at h

end Circuit

end MovingProjection.MonotoneCircuitMarkov
