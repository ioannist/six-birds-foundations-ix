import MovingProjection.MonotoneCircuitMarkov
import Mathlib.Data.Nat.Log

/-! A bounded-record emitter for the monotone-circuit reduction. Each output
request uses the fixed header and at most one input gate record. -/

namespace MovingProjection.MonotoneCircuitMarkov.Encoding

variable {n : ℕ}

def markId : Mark n → ℕ
  | .anchor => 0
  | .sentinel => 1
  | .wire i => i.val + 2

theorem markId_lt (m : Mark n) : markId m < n + 2 := by
  cases m with
  | anchor => simp [markId]
  | sentinel => simp [markId]
  | wire i => exact Nat.add_lt_add_right i.isLt 2

theorem markId_injective : Function.Injective (markId (n := n)) := by
  intro m k h
  cases m <;> cases k <;> simp [markId] at h ⊢
  exact Fin.ext h

def slotId (i : Fin n) (slot : Bool) : ℕ :=
  1 + 2*i.val + slot.toNat

theorem slotId_lt (i : Fin n) (slot : Bool) : slotId i slot < 2*n+1 := by
  have hi := i.isLt
  cases slot <;> simp [slotId] <;> omega

theorem slotId_injective :
    Function.Injective (fun p : Fin n × Bool => slotId p.1 p.2) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  suffices hv : i.val = j.val ∧ b = c from Prod.ext (Fin.ext hv.1) hv.2
  cases b <;> cases c <;> simp [slotId] at h ⊢ <;> omega

inductive Request (n : ℕ) where
  | header
  | geometry
  | mark (m : Mark n)
  | output
  | gate (i : Fin n) (slot : Bool)
  | publication

/-- The header and the single admissible catalogue set suffice for the
constant data. Mark and licence tables are emitted explicitly. -/
def header (n : ℕ) : List ℕ := [0,n+2,2,1,1,3,1,n+2,1,2,2*n+1,1]
def geometry : List ℕ := [1,1,1,1,0,1,1,0,0,1]
def publication : List ℕ := [4,0,0,0,0,1,4,1,1]

def markRecord (m : Mark n) : List ℕ :=
  [2,markId m,markId m,1,n+2,0,(decide (m = sentinel)).toNat,1,4,
    1,1,1,1,1,1,1,1]

def licenceRecord (id : ℕ) (left right : List (Mark n)) : List ℕ :=
  [3,id] ++ left.map markId ++ right.map markId ++ [1,1,1]

def gateRecord (i : Fin n) (slot : Bool) (gate : Gate (Fin n)) : List ℕ :=
  match gate with
  | .const true => licenceRecord (n := n) (slotId i slot) [anchor,anchor,anchor] [anchor,anchor,anchor]
  | .const false => licenceRecord (slotId i slot) [wire i,anchor,anchor] [anchor,anchor,anchor]
  | .conj a b =>
    let t := wire (if slot then b else a)
    licenceRecord (slotId i slot) [wire i,t,anchor] [anchor,t,anchor]
  | .disj a b => licenceRecord (slotId i slot) [wire i,wire a,wire b] [anchor,wire a,wire b]

/-- At a gate slot only the corresponding input gate is read. The other
requests read no gate. The distinguished output is a header field. -/
def emit (out : Fin n) (read : Fin n → Gate (Fin n)) : Request n → List ℕ
  | .header => header n
  | .geometry => geometry
  | .mark m => markRecord m
  | .output => licenceRecord 0 [sentinel,sentinel,wire out] [anchor,anchor,wire out]
  | .gate i slot => gateRecord i slot (read i)
  | .publication => publication

/-- The next request is computed from a single output-record cursor. -/
def requestAt (k : Fin (3*n+6)) : Request n :=
  if _h0 : k.val = 0 then .header else
  if _h1 : k.val = 1 then .geometry else
  if _h2 : k.val = 2 then .mark anchor else
  if _h3 : k.val = 3 then .mark sentinel else
  if h : k.val < n+4 then
    .mark (wire ⟨k.val - 4,by omega⟩)
  else if _hout : k.val = n+4 then .output
  else if h : k.val < 3*n+5 then
    let d := k.val - (n+5)
    .gate ⟨d / 2,by dsimp [d]; omega⟩ (decide (d % 2 = 1))
  else .publication

theorem requestAt_wire (i : Fin n) :
    requestAt (n := n) ⟨i.val+4,by have := i.isLt; omega⟩ = .mark (wire i) := by
  have hi := i.isLt
  have h1 : i.val+4 ≠ 1 := by omega
  have h2 : i.val+4 ≠ 2 := by omega
  have h3 : i.val+4 ≠ 3 := by omega
  simp [requestAt,h1,h2,h3,Nat.add_lt_add_right hi 4]

theorem requestAt_output (n : ℕ) :
    requestAt (n := n) ⟨n+4,by omega⟩ = .output := by
  have h1 : n+4 ≠ 1 := by omega
  have h2 : n+4 ≠ 2 := by omega
  have h3 : n+4 ≠ 3 := by omega
  simp [requestAt,h1,h2,h3]

theorem requestAt_gate (i : Fin n) (b : Bool) :
    requestAt (n := n) ⟨n+5 + 2*i.val + b.toNat, by
      have h := slotId_lt i b
      simp only [slotId] at h
      omega⟩ = .gate i b := by
  have h0 : n+5+2*i.val+b.toNat ≠ 0 := by omega
  have h1 : n+5+2*i.val+b.toNat ≠ 1 := by omega
  have h2 : n+5+2*i.val+b.toNat ≠ 2 := by omega
  have h3 : n+5+2*i.val+b.toNat ≠ 3 := by omega
  have h4 : ¬ n+5+2*i.val+b.toNat < n+4 := by omega
  have h5 : n+5+2*i.val+b.toNat ≠ n+4 := by omega
  have h6 : n+5+2*i.val+b.toNat < 3*n+5 := by
    have h := slotId_lt i b
    simp only [slotId] at h
    omega
  have hd : n+5+2*i.val+b.toNat - (n+5) = 2*i.val+b.toNat := by omega
  simp only [requestAt,h0,h1,h2,h3,h4,h5,h6,dif_pos,
    hd]
  have q : (2*i.val+b.toNat)/2 = i.val := by
    cases b
    all_goals simp
    all_goals omega
  have r : decide ((2*i.val+b.toNat)%2 = 1) = b := by cases b <;> simp
  exact congrArg₂ Request.gate (Fin.ext q) r

theorem requestAt_publication (n : ℕ) :
    requestAt (n := n) ⟨3*n+5,by omega⟩ = .publication := by
  have h1 : 3*n+5 ≠ 1 := by omega
  have h2 : 3*n+5 ≠ 2 := by omega
  have h3 : 3*n+5 ≠ 3 := by omega
  have h4 : ¬ 3*n+5 < n+4 := by omega
  have h5 : 3*n+5 ≠ n+4 := by omega
  simp [requestAt,h1,h2,h3,h4,h5]

def stream (C : Circuit n) : List (List ℕ) := List.ofFn (fun k => emit C.out C.gate (requestAt k))

/-- One transition writes a single record and advances the cursor. The final
cursor is the halt state. No prefix of the output is kept in the state. -/
def step (out : Fin n) (read : Fin n → Gate (Fin n)) (k : Fin (3*n+7)) :
    Option (List ℕ × Fin (3*n+7)) :=
  if h : k.val < 3*n+6 then
    some (emit out read (requestAt ⟨k.val,h⟩),⟨k.val+1,by omega⟩)
  else none

theorem step_matches_stream (C : Circuit n) (k : Fin (3*n+6)) :
    step C.out C.gate k.castSucc =
      some ((stream C)[k.val]'(by simpa only [stream,List.length_ofFn] using k.isLt),
        ⟨k.val+1,by have := k.isLt; omega⟩) := by
  simp only [step,Fin.val_castSucc,k.isLt,dif_pos,stream,List.getElem_ofFn]

theorem step_halts (C : Circuit n) :
    step C.out C.gate ⟨3*n+6,by omega⟩ = none := by simp [step]

theorem output_record_correct (C : Circuit n) :
    emit C.out C.gate .output =
      licenceRecord 0 (C.instrument.license (.inl ())).left
        (C.instrument.license (.inl ())).right := rfl

theorem gate_record_correct (C : Circuit n) (i : Fin n) (slot : Bool) :
    emit C.out C.gate (.gate i slot) =
      licenceRecord (slotId i slot) (C.instrument.license (.inr (i,slot))).left
        (C.instrument.license (.inr (i,slot))).right := by
  cases h : C.gate i with
  | const b =>
    cases b <;> simp [emit,gateRecord,Circuit.instrument,Circuit.pair,Circuit.gatePair,
      Circuit.gateHead,Circuit.guards,TimedPair.left,TimedPair.right,h]
  | conj | disj =>
    simp [emit,gateRecord,Circuit.instrument,Circuit.pair,Circuit.gatePair,
      Circuit.gateHead,Circuit.guards,TimedPair.left,TimedPair.right,h]

theorem mark_record_correct (C : Circuit n) (m : Mark n) :
    (C.endpoint false).law.rate m = 1 / (n + 2 : ℚ) ∧
    (C.endpoint true).law.rate m = 1 / (n + 2 : ℚ) ∧
    (C.endpoint false).law.spectrum (coord m) = 1/4 ∧
    (C.endpoint true).law.spectrum (coord m) =
      (if (decide (m = sentinel)).toNat = 1 then (-1/4 : ℚ) else 1/4) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  by_cases h : m = sentinel <;> simp [Circuit.endpoint,Circuit.endpointLaw,Circuit.spectrum,coord,h]

private theorem licence_bounds {id : ℕ} (hi : id < 2*n+16)
    (u v : List (Mark n)) (hu : u.length = 3) (hv : v.length = 3) :
    (licenceRecord id u v).length ≤ 17 ∧ ∀ a ∈ licenceRecord id u v, a < 2*n+16 := by
  refine ⟨by simp [licenceRecord,hu,hv], ?_⟩
  intro a ha
  simp only [licenceRecord,List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · simp at ha
    omega
  · obtain ⟨m,_,rfl⟩ := List.mem_map.mp ha
    have h := markId_lt m
    omega
  · obtain ⟨m,_,rfl⟩ := List.mem_map.mp ha
    have h := markId_lt m
    omega
  · simp at ha
    omega

/-- A request produces at most seventeen natural fields. Each fits into a
word of logarithmic width, including counts, mark numbers and licence IDs. -/
theorem emit_bounds (out : Fin n) (read : Fin n → Gate (Fin n)) (r : Request n) :
    (emit out read r).length ≤ 17 ∧ ∀ a ∈ emit out read r, a < 2*n+16 := by
  cases r with
  | header =>
    constructor
    · simp [emit,header]
    · intro a ha
      simp [emit,header] at ha
      omega
  | geometry | publication =>
    constructor
    · simp [emit,geometry,publication]
    · intro a ha
      simp [emit,geometry,publication] at ha
      omega
  | mark m =>
    constructor
    · simp [emit,markRecord]
    · intro a ha
      have hm := markId_lt m
      have hb : (decide (m = sentinel)).toNat ≤ 1 := by
        by_cases h : m = sentinel <;> simp [h]
      simp [emit,markRecord] at ha
      omega
  | output => exact licence_bounds (by omega) _ _ rfl rfl
  | gate i slot =>
    have hi := slotId_lt i slot
    have h : slotId i slot < 2*n+16 := by omega
    cases e : read i with
    | const b =>
      cases b <;> simp only [emit,gateRecord,e] <;> exact licence_bounds h _ _ rfl rfl
    | conj | disj =>
      simp only [emit,gateRecord,e]
      exact licence_bounds h _ _ rfl rfl

/-- One word can hold each field when the input has at least one record
per gate. Each natural field has a binary expansion of at most this width. -/
def fieldWidth (inputLength : ℕ) : ℕ := Nat.log2 (4*(inputLength+16)) + 1

theorem fields_fit_bits {inputLength : ℕ} (hn : n ≤ inputLength) (C : Circuit n)
    (r : Request n) {a : ℕ} (ha : a ∈ emit C.out C.gate r) :
    a < 2 ^ fieldWidth inputLength := by
  have h := (emit_bounds C.out C.gate r).2 a ha
  have hs : 2*n+16 ≤ 4*(inputLength+16) := by omega
  exact (h.trans_le hs).trans (Nat.lt_log2_self)

theorem stream_length (C : Circuit n) : (stream C).length = 3*n+6 := by
  simp [stream]

theorem cursor_fits_bits {inputLength : ℕ} (hn : n ≤ inputLength) (k : Fin (3*n+7)) :
    k.val < 2 ^ fieldWidth inputLength := by
  have h : k.val < 4*(inputLength+16) := by
    have := k.isLt
    omega
  exact h.trans Nat.lt_log2_self

/-- The indexed reduction supplies distinct lawful endpoints in the
single-word event model and emits only logarithmic-width fields. The
input length counts at least one symbol per gate. -/
theorem checked_reduction {inputLength : ℕ} (hn : n ≤ inputLength) (C : Circuit n) :
    (stream C).length = 3*n+6 ∧
    (∀ row ∈ stream C, row.length ≤ 17 ∧ ∀ a ∈ row, a < 2 ^ fieldWidth inputLength) ∧
    C.endpoint false ≠ C.endpoint true ∧
    ((EventExperiments.ofNative C.instrument).Factorable
      (EventExperiments.liftNative C.instrument (C.endpoint false))
      (EventExperiments.liftNative C.instrument (C.endpoint true)) ↔
      C.value C.out = true) := by
  refine ⟨stream_length C, ?_, C.endpoints_distinct, ?_⟩
  · intro row hr
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨(emit_bounds C.out C.gate (requestAt k)).1, fun _ ha =>
      fields_fit_bits hn C (requestAt k) ha⟩
  · exact (EventExperiments.factorable_ofNative_iff C.instrument _ _).trans C.native_fine_iff_value

end MovingProjection.MonotoneCircuitMarkov.Encoding
