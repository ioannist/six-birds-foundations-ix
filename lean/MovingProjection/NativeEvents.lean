import MovingProjection.Experiments
import MovingProjection.OneStateEvents

/-! Fixed-profile joint-mass predicates on the one-state native protocol.
The underlying instrument has empty license and publication catalogues.
The extra predicates restrict states externally. The step relation uses the
native rewrite metric. The native horizon field does not constrain these
external predicates. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

variable {M : Type*} [Fintype M] [DecidableEq M]

def singletonParity : ParityBasis Empty Unit where
  value i := i.elim
  abs_eq_one i := i.elim
  balance i := i.elim
  orthogonal i := i.elim

def instrument (floor : ℚ) (hfloor : 0 < floor) :
    NativeExperiments M Empty Unit Unit Empty Empty where
  parity := singletonParity
  weights := fun _ => 1
  weights_pos := fun _ => by norm_num
  weights_unit := by simp
  reversal := id
  reversal_involutive := fun _ => rfl
  δ := floor
  δ_pos := hfloor
  κ := 0
  κ_lt_one := zero_lt_one
  horizon := 2
  license i := i.elim
  audit i := i.elim
  policy := fun _ => True

abbrev NativeState (floor : ℚ) (hfloor : 0 < floor) :=
  ((instrument (M := M) floor hfloor).protocol).State 0

def stateProfile : Capabilities M Unit Unit Empty Empty 0 where
  mask := OrderDual.toDual Set.univ
  grades := fun _ => OrderDual.toDual ⊤
  licenses := ∅
  published := ∅

def law (rate : M → ℚ) : PhysicalLaw M Empty Unit Unit where
  rate := rate
  spectrum := fun p => p.2.elim
  register := fun _ _ _ _ _ => 1

omit [Fintype M] [DecidableEq M] in
theorem law_marked (rate : M → ℚ) (m : M) (x y : Unit × Unit) :
    (law rate).marked singletonParity m x y = rate m := by
  simp [PhysicalLaw.marked, nativeMarked, law, ParityBasis.kernel]

theorem native_word_mass {floor : ℚ} {hfloor : 0 < floor} (s : NativeState (M := M) floor hfloor)
    (word : Word M) :
    (∑ z : Unit × Unit, s.law.marked singletonParity word.1 ((), ()) z *
      s.law.marked singletonParity word.2 z ((), ())) = wordMass s.law.rate word := by
  have he : s.law = law s.law.rate := by
    apply PhysicalLaw.ext
    · rfl
    · funext p
      exact p.2.elim
    · funext m x y u v
      have hv := s.legal.2.2.2.2.1.2.1 m x y u
      simpa [law] using hv
  calc
    _ = wordMass (law s.law.rate).rate word := by
      rw [he]
      simp only [law_marked]
      simp [wordMass, law]

/-- The joint-mass comparison of the measured events equals the corresponding
comparison of rate products. Both sides contain words of duration two. -/
theorem native_test_holds_iff {floor : ℚ} {hfloor : 0 < floor}
    (s : NativeState (M := M) floor hfloor) (test : Test M) :
    (let mass (w : Word M) :=
        ∑ z : Unit × Unit, s.law.marked singletonParity w.1 ((), ()) z *
          s.law.marked singletonParity w.2 z ((), ())
     match test with
     | .equal l r => mass l = mass r
     | .sum l r t _ => mass l = mass r + mass t) ↔ test.holds s.law.rate := by
  cases test <;> simp only [native_word_mass, Test.holds]

/-- A lawful point in the event simplex gives a state of the native instrument
with full support and the unique one-state disclosure relation. -/
noncomputable def toNative {tests : List (Test M)} {floor : ℚ} (hfloor : 0 < floor)
    {rate : M → ℚ} (hrate : Lawful tests floor rate) : NativeState (M := M) floor hfloor := by
  refine ⟨stateProfile, law rate, ?_⟩
  refine ⟨?_, trivial, ?_, ?_, ?_, ?_⟩
  · intro _ _ _
    exact le_rfl
  · refine ⟨hrate.2.1, hrate.1, ?_⟩
    simp [Protocol.fiber, ProbeCatalog.rateTests, instrument, NativeExperiments.protocol,
      stateProfile]
  · constructor
    · simp [Protocol.fiber, ProbeCatalog.spectralTests, instrument, NativeExperiments.protocol,
        stateProfile]
    · intro budget hbudget
      simp only [spectrumBudgets, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hbudget
      obtain ⟨mark, rfl⟩ := hbudget
      simp [law, instrument, NativeExperiments.protocol]
  · simp [RegisterValid, law, instrument, NativeExperiments.protocol]
  · ext e
    simp [Protocol.fiber, stateProfile, registerMask, law]

abbrev ProfileState (held : (M → ℚ) → Prop) (floor : ℚ) (hfloor : 0 < floor) :=
  {s : NativeState (M := M) floor hfloor //
    s.profile = stateProfile ∧ held s.law.rate}

def ProfileStep {held : (M → ℚ) → Prop} {floor : ℚ} {hfloor : 0 < floor}
    (ε : ℚ) (a b : ProfileState held floor hfloor) : Prop :=
  ∃ e, (instrument floor hfloor).protocol.Step ε e a.1 b.1

theorem ProfileStep.mono {held : (M → ℚ) → Prop} {floor : ℚ} {hfloor : 0 < floor}
    {ε η : ℚ} {a b : ProfileState held floor hfloor}
    (h : ProfileStep ε a b) (hle : ε ≤ η) : ProfileStep η a b := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  by_cases hr : e = .rewrite
  · subst e
    simp only [Protocol.Step, if_true] at he ⊢
    exact ⟨he.1, fun m s t => (he.2 m s t).trans_le hle⟩
  · simpa only [Protocol.Step, if_neg hr] using he

abbrev EventState (tests : List (Test M)) (floor : ℚ) (hfloor : 0 < floor) :=
  ProfileState (fun rate => ∀ test ∈ tests, test.holds rate) floor hfloor

abbrev NativeEventStep {tests : List (Test M)} {floor : ℚ} {hfloor : 0 < floor}
    (ε : ℚ) (a b : EventState tests floor hfloor) : Prop :=
  ProfileStep ε a b

theorem event_state_rate_lawful {tests : List (Test M)} {floor : ℚ} {hfloor : 0 < floor}
    (a : EventState tests floor hfloor) : Lawful tests floor a.1.law.rate :=
  ⟨a.1.legal.2.2.1.2.1, a.1.legal.2.2.1.1, a.2.2⟩

noncomputable def liftEventState {tests : List (Test M)} {floor : ℚ} (hfloor : 0 < floor)
    (rate : {rate : M → ℚ // Lawful tests floor rate}) : EventState tests floor hfloor :=
  ⟨toNative hfloor rate.2, rfl, rate.2.2.2⟩

theorem lift_event_state_readback {tests : List (Test M)} {floor : ℚ} {hfloor : 0 < floor}
    (a : EventState tests floor hfloor) :
    liftEventState hfloor ⟨a.1.law.rate, event_state_rate_lawful a⟩ = a := by
  apply Subtype.ext
  apply Protocol.State.ext
  · exact a.2.1.symm
  · apply PhysicalLaw.ext
    · rfl
    · funext p
      exact p.2.elim
    · funext m x y u v
      have hv := a.1.legal.2.2.2.2.1.2.1 m x y u
      simpa [liftEventState, toNative, law] using hv.symm

theorem native_event_step_iff {tests : List (Test M)} {floor : ℚ} {hfloor : 0 < floor}
    {ε : ℚ} {a b : EventState tests floor hfloor} :
    NativeEventStep ε a b ↔ SmallStep tests floor ε a.1.law.rate b.1.law.rate := by
  obtain ⟨rate, hrate⟩ := (show ∃ rate : {r : M → ℚ // Lawful tests floor r},
      liftEventState hfloor rate = a from ⟨_, lift_event_state_readback a⟩)
  obtain ⟨other, hother⟩ := (show ∃ rate : {r : M → ℚ // Lawful tests floor r},
      liftEventState hfloor rate = b from ⟨_, lift_event_state_readback b⟩)
  subst a b
  unfold NativeEventStep
  have hnear : PhysicalNear singletonParity ε (law rate.1) (law other.1) ↔
      ∀ m, |rate.1 m - other.1 m| < ε := by
    simp only [PhysicalNear, law_marked]
    exact ⟨fun h m => h m ((), ()) ((), ()), fun h m _ _ => h m⟩
  change (∃ e, (instrument floor hfloor).protocol.Step ε e (toNative hfloor rate.2)
      (toNative hfloor other.2)) ↔ SmallStep tests floor ε rate.1 other.1
  constructor
  · rintro ⟨e, he⟩
    have here : e = .rewrite := by
      by_contra hn
      simp only [Protocol.Step, if_neg hn] at he
      exact (irrefl stateProfile) he.1.1
    subst e
    exact ⟨rate.2, other.2, hnear.mp (he.2)⟩
  · intro h
    exact ⟨.rewrite, rfl, hnear.mpr h.2.2⟩

theorem native_event_chain_iff {tests : List (Test M)} {floor : ℚ} {hfloor : 0 < floor}
    {ε : ℚ} {a b : EventState tests floor hfloor} :
    Relation.ReflTransGen (NativeEventStep ε) a b ↔
      Chain tests floor ε a.1.law.rate b.1.law.rate := by
  constructor
  · intro h
    exact h.lift (fun s => s.1.law.rate) (fun _ _ hs => native_event_step_iff.mp hs)
  · intro h
    classical
    let lift (r : M → ℚ) : EventState tests floor hfloor :=
      if H : Lawful tests floor r then liftEventState hfloor ⟨r, H⟩ else a
    have hlawful (r : M → ℚ) (hr : Lawful tests floor r) : (lift r).1.law.rate = r := by
      simp [lift, hr, liftEventState, toNative, law]
    have ha : lift a.1.law.rate = a := by
      simpa [lift, event_state_rate_lawful a] using lift_event_state_readback a
    have hb : lift b.1.law.rate = b := by
      simpa [lift, event_state_rate_lawful b] using lift_event_state_readback b
    have H := h.lift lift (fun p q hpq => by
      apply (native_event_step_iff (a := lift p) (b := lift q) (ε := ε)).mpr
      rwa [hlawful p hpq.1, hlawful q hpq.2.1])
    rwa [ha, hb] at H

end MovingProjection.OneStateEvents
