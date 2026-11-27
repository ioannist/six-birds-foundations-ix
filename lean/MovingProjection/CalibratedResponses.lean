import MovingProjection.SingleAdditiveLicence

/-! A duration-one additive comparison fixes the rates and supplies a
complementary pair of responses at each probe. The other comparisons involve
only the marks with the common rate. -/

namespace MovingProjection.CalibratedResponses

open scoped BigOperators

abbrev Other (M : Type*) := Bool ⊕ M
abbrev Mark (M : Type*) := Unit ⊕ Other M

def left : Mark M := .inl ()
def toggle (b : Bool) : Mark M := .inr (.inl b)

variable {M I X Γ Δ : Type*} [Fintype M] [Fintype I] [Fintype X] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq X] [Nonempty X]

structure Catalogue (M I Γ Δ : Type*) where
  horizon : ℕ
  pair : Γ → TimedPair (Other M) (horizon + 1)
  audit : Δ → (Other M × I) × ℚ
  amplitude : ℚ

def floor (M : Type*) [Fintype M] : ℚ := 1 / ((Fintype.card M : ℚ) + 4)

omit [DecidableEq M] in
theorem floor_pos : 0 < floor M := by unfold floor; positivity

def rate : Mark M → ℚ
  | .inl _ => 2 * floor M
  | .inr _ => floor M

omit [DecidableEq M] in
theorem floor_le_rate (m : Mark M) : floor M ≤ rate m := by
  cases m <;> simp only [rate] <;> linarith [floor_pos (M := M)]

omit [DecidableEq M] in
theorem rate_sum : ∑ m : Mark M, rate m = 1 := by
  simp only [Fintype.sum_sum_type, rate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_sum, Fintype.card_bool, Fintype.card_unit, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  unfold floor
  have hn : (Fintype.card M : ℚ) + 4 ≠ 0 := by positivity
  field_simp
  ring

omit [DecidableEq M] in
theorem rate_forced (θ : Mark M → ℚ) (hs : ∑ m, θ m = 1)
    (hf : ∀ m, floor M ≤ θ m)
    (ha : θ left = θ (toggle false) + θ (toggle true)) : θ = rate := by
  have hle (m : Mark M) : rate m ≤ θ m := by
    rcases m with (⟨⟩ | m)
    · change 2 * floor M ≤ θ left
      linarith [hf (toggle false), hf (toggle true)]
    · exact hf _
  have hsum : ∑ m, (θ m - rate m) = 0 := by rw [Finset.sum_sub_distrib, hs, rate_sum, sub_self]
  funext m
  have hm := Finset.single_le_sum (s := Finset.univ) (f := fun j => θ j - rate j)
    (fun j _ => sub_nonneg.mpr (hle j)) (Finset.mem_univ m)
  rw [hsum] at hm
  linarith [hle m]

variable (C : Catalogue M I Γ Δ)

def comparison : Unit ⊕ Γ → TimedPair (Mark M) (C.horizon + 1)
  | .inl _ => ⟨left, toggle false, [], [], rfl, Nat.succ_le_succ (Nat.zero_le _)⟩
  | .inr g => ⟨.inr (C.pair g).first, .inr (C.pair g).next, (C.pair g).tail.map Sum.inr,
      (C.pair g).other.map Sum.inr, by simpa using (C.pair g).duration, by simpa using (C.pair g).fits⟩

def second : (g : Unit ⊕ Γ) → Option (SecondWord (comparison C g))
  | .inl _ => some ⟨[toggle true], rfl, by simp [comparison, TimedPair.right, toggle]⟩
  | .inr _ => none

def audit : I ⊕ Δ → AuditQuery (Mark M) I (C.horizon + 1)
  | .inl j => .calibration left j (C.amplitude / 2)
  | .inr e => .calibration (.inr (C.audit e).1.1) (C.audit e).1.2 (C.audit e).2

def instrument (B : ParityBasis I X) :
    EventExperiments (Mark M) I X Unit (Unit ⊕ Γ) (I ⊕ Δ) where
  native := {
    parity := B
    weights := fun _ => 1
    weights_pos := fun _ => by norm_num
    weights_unit := by simp
    reversal := id
    reversal_involutive := fun _ => rfl
    δ := floor M
    δ_pos := floor_pos
    κ := 1 / 2
    κ_lt_one := by norm_num
    horizon := C.horizon + 1
    license := comparison C
    audit := audit C
    policy := fun held => held = Finset.univ
  }
  second := second C

abbrev State (B : ParityBasis I X) := (instrument C B).State 0

def profile : Capabilities (Mark M) X Unit (Unit ⊕ Γ) (I ⊕ Δ) 0 :=
  ⟨OrderDual.toDual Set.univ, fun _ => OrderDual.toDual ⊤, Finset.univ, Finset.univ⟩

def response (w : List (Other M)) (x : Mark M × I → ℚ) (i : I) : ℚ :=
  (w.map (fun m => x (.inr m,i))).prod

structure Catalogue.Lawful (x : Mark M × I → ℚ) : Prop where
  budget : ∀ m, (∑ j, |x (m,j)|) ≤ 1/2
  control : ∀ j, x (left,j) = C.amplitude / 2
  calibrations : ∀ e, x (.inr (C.audit e).1.1,(C.audit e).1.2) = (C.audit e).2
  complement : ∀ j, x (toggle false,j) + x (toggle true,j) = C.amplitude
  comparisons : ∀ g j, response (C.pair g).left x j = response (C.pair g).right x j

omit [Fintype I] [Fintype Δ] [DecidableEq M] [DecidableEq X] [Nonempty X] in
theorem exactly_one (B : ParityBasis I X) :
    ∃! g, ((instrument C B).second g).isSome = true := by
  refine ⟨.inl (), rfl, ?_⟩
  rintro (u | g) hg
  · cases u
    rfl
  · exact False.elim (Bool.noConfusion hg)

variable {C} {B : ParityBasis I X}

theorem rates_eq (s : State C B) (hp : s.val.profile = profile) : s.val.law.rate = rate := by
  have h (x : X × Unit) (y : X) := s.property (.inl ()) (by rw [hp]; exact Finset.mem_univ _) _ rfl x y
  have he := (SingleAdditiveLicence.joint_words_iff B _ s.val.legal.2.2.2.2.1.2.1
    left (toggle false) (toggle true) [] [] []).mp h
  apply rate_forced _ s.val.legal.2.2.1.2.1 s.val.legal.2.2.1.1
  simpa using he.1

theorem lawful_state (s : State C B) (hp : s.val.profile = profile) :
    C.Lawful s.val.law.spectrum := by
  let D := (instrument C B).base
  have hl (i : I) : s.val.law.spectrum (left,i) = C.amplitude/2 :=
    D.calibration_value s.val (by rw [hp]; exact Finset.mem_univ (.inl i)) rfl
  refine ⟨spectrum_budget s.val.legal.2.2.2.1, hl, ?_, ?_, ?_⟩
  · intro e
    exact D.calibration_value s.val (by rw [hp]; exact Finset.mem_univ (.inr e)) rfl
  · intro i
    have h (x : X × Unit) (y : X) := s.property (.inl ()) (by rw [hp]; exact Finset.mem_univ _) _ rfl x y
    have he := (SingleAdditiveLicence.joint_words_iff B _ s.val.legal.2.2.2.2.1.2.1
      left (toggle false) (toggle true) [] [] []).mp h
    have hi := he.2 i
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      rates_eq s hp, hl] at hi
    change 2 * floor M * (C.amplitude / 2) =
      floor M * s.val.law.spectrum (toggle false,i) + floor M * s.val.law.spectrum (toggle true,i)
      at hi
    rw [← mul_add, show 2 * floor M * (C.amplitude/2) = floor M * C.amplitude by ring] at hi
    exact (mul_left_cancel₀ (floor_pos (M := M)).ne' hi).symm
  · intro g j
    have hlaw := D.license_measured s.val (g := .inr g) (by rw [hp]; exact Finset.mem_univ _)
    have he := (B.word_identity_iff (fun m i => s.val.law.spectrum (m,i)) _ _ _ _).mp hlaw.2 j
    simpa [D, instrument, EventExperiments.base, EventExperiments.basePair, comparison,
      second, TimedPair.left, TimedPair.right, response, List.map_map, Function.comp_def] using he

def law (x : Mark M × I → ℚ) : PhysicalLaw (Mark M) I X Unit :=
  ⟨rate, x, fun _ _ _ _ _ => 1⟩

omit [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq I] in
private theorem law_rate_comparison (g : Γ) :
    (((comparison C (.inr g)).left.map rate).prod) = (((comparison C (.inr g)).right.map rate).prod) := by
  have he (w : List (Other M)) : (((w.map (Sum.inr : Other M → Mark M)).map rate).prod) =
      (floor M) ^ w.length := by
    induction w with
    | nil => simp
    | cons m w ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, rate, ih, pow_succ, mul_comm]
  change ((((C.pair g).left.map Sum.inr).map rate).prod) =
    ((((C.pair g).right.map Sum.inr).map rate).prod)
  rw [he, he]
  simp only [TimedPair.left, TimedPair.right, List.length_cons, (C.pair g).duration]

omit [DecidableEq X] [Nonempty X] in
set_option maxHeartbeats 800000 in
private theorem build_legal (x : Mark M × I → ℚ) (hx : C.Lawful x) :
    (instrument C B).base.protocol.legal profile (law x) := by
  let D := (instrument C B).base
  refine ⟨fun _ _ _ => le_rfl, rfl, ⟨floor_le_rate, rate_sum, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro test ht
    change test ∈ D.protocol.checks.rateTests Finset.univ Finset.univ at ht
    simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at ht
    rcases ht with ⟨g, _, hg⟩ | ⟨e, _, he⟩
    · change test ∈ [⟨routeRateRow (D.license g).left (D.license g).right, 1⟩] at hg
      obtain rfl := List.mem_singleton.mp hg
      apply (route_rate_compile _ _ _ _).mpr
      rcases g with (u | g)
      · change (List.map rate [left]).prod = 1 * (List.map rate [left]).prod
        exact (one_mul _).symm
      · simpa only [one_mul] using law_rate_comparison (C := C) g
    · rcases e with (i | e) <;> cases he
  · intro test ht
    change test ∈ D.protocol.checks.spectralTests Finset.univ Finset.univ at ht
    simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap] at ht
    rcases ht with (hr | ⟨g, _, hg⟩) | ⟨e, _, he⟩
    · change test ∈ Finset.univ.toList.map (reversalTest (id : Mark M → Mark M)) at hr
      obtain ⟨⟨m,i⟩,_,rfl⟩ := List.mem_map.mp hr
      simp [reversalTest, MonomialTest.holds]
    · change test ∈ Finset.univ.toList.map
        (routeCharacterTest (D.license g).left (D.license g).right) at hg
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      rcases g with (u | g)
      · change (routeCharacterTest [left] [left] i).holds x
        simp [routeCharacterTest, MonomialTest.holds]
      · change (routeCharacterTest (comparison C (.inr g)).left
            (comparison C (.inr g)).right i).holds (fun mi => x (mi.1,mi.2))
        simp only [MonomialTest.holds, routeCharacterTest, one_mul,
          character_monomial _ _ (fun m j => x (m,j))]
        simpa [D, instrument, EventExperiments.base, EventExperiments.basePair, comparison,
          second, TimedPair.left, TimedPair.right, response, List.map_map, Function.comp_def] using
            hx.comparisons g i
    · have ha : ∃ m i a, D.audit e = .calibration m i a ∧ x (m,i) = a := by
        rcases e with (i | e)
        · exact ⟨left, i, _, rfl, hx.control i⟩
        · exact ⟨_, _, _, rfl, hx.calibrations e⟩
      obtain ⟨m,i,a,ha,hx'⟩ := ha
      dsimp only [NativeExperiments.protocol] at he
      rw [ha] at he
      obtain rfl := List.mem_singleton.mp he
      change monomial (pointExponent (m,i)) x = a * monomial (fun _ => 0) x
      rw [pointMonomial, hx']
      simp [monomial]
  · intro budget hbudget
    unfold spectrumBudgets at hbudget
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hbudget
    change (∑ i ∈ Finset.univ.map _, |x i|) ≤ 1/2
    rw [Finset.sum_map]
    exact hx.budget m
  · simp [RegisterValid, law, EventExperiments.base, instrument, NativeExperiments.protocol]
  · ext e
    simp [Protocol.fiber, profile, registerMask, law]

noncomputable def build (B : ParityBasis I X) (x : Mark M × I → ℚ) (hx : C.Lawful x) : State C B := by
  refine ⟨⟨profile, law x, build_legal x hx⟩, ?_⟩
  intro g _ w hg
  cases g with
  | inl u =>
    cases u
    let extra : SecondWord (comparison C (.inl ())) :=
      ⟨[toggle true], rfl, by simp [comparison, TimedPair.right, toggle]⟩
    change some extra = some w at hg
    have hw := Option.some.inj hg
    subst w
    apply (SingleAdditiveLicence.joint_words_iff B (law x) (by simp [law])
      left (toggle false) (toggle true) [] [] []).mpr
    constructor
    · simp [law, rate, left, toggle]
      ring
    · intro i
      have ht := hx.complement i
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      change (2 * floor M) * x (left,i) =
        floor M * x (toggle false,i) + floor M * x (toggle true,i)
      rw [hx.control i, ← mul_add, ht]
      ring
  | inr g => cases hg

theorem build_decode (s : State C B) (hp : s.val.profile = profile) :
    build B s.val.law.spectrum (lawful_state s hp) = s := by
  apply Subtype.ext
  refine Protocol.State.ext (show profile = s.val.profile from hp.symm) ?_
  apply PhysicalLaw.ext
  · exact (rates_eq s hp).symm
  · rfl
  · funext m x y u v
    simpa [law] using (s.val.legal.2.2.2.2.1.2.1 m x y u).symm

end MovingProjection.CalibratedResponses
