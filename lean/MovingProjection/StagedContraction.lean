import MovingProjection.Example
import MovingProjection.NativeWords

/-! An audited source on which the active damping equations must be recomputed. -/

namespace MovingProjection.StagedContraction

open scoped BigOperators

abbrev Mark := Example.Mark
abbrev Cell := Example.Cell
abbrev Index := Mark × Unit

def gateIndex : Index := (0, ())
def responseIndex : Index := (1, ())
def auditIndex : Index := (2, ())

def pair : TimedPair Mark 2 := ⟨0, 0, [1], [2], rfl, by decide⟩

def instrument : NativeExperiments Mark Unit Bool Cell Unit Unit where
  parity := Example.parity
  weights := Example.experiment.weights
  weights_pos := Example.experiment.weights_pos
  weights_unit := Example.experiment.weights_unit
  reversal := id
  reversal_involutive := fun _ => rfl
  δ := 1/8
  κ := 1/2
  δ_pos := by norm_num
  κ_lt_one := by norm_num
  horizon := 2
  license := fun _ => pair
  audit := fun _ => .calibration 2 () (1/4)
  policy := fun _ => True

noncomputable abbrev D := instrument.protocol
abbrev State := D.State 1

def profile : Capabilities Mark Bool Cell Unit Unit 1 where
  mask := (Example.capabilities true true true false false).mask
  grades := (Example.capabilities true true true false false).grades
  licenses := {()}
  published := {()}

def spectrum (x y : ℚ) (p : Index) : ℚ :=
  match p.1.val with
  | 0 => x
  | 1 => y
  | 2 => 1/4
  | _ => 0

def law (x y : ℚ) : PhysicalLaw Mark Unit Bool Cell :=
  ⟨fun _ => 1/4, spectrum x y, Example.table true⟩

def routeTest : MonomialTest Index := routeCharacterTest [0, 1] [0, 2] ()
def auditTest : MonomialTest Index := calibrationTest 2 () (1/4)

private theorem test_mem (test : MonomialTest Index) :
    test ∈ (D.fiber profile).spectralChecks ↔
      (∃ i, test = reversalTest id i) ∨ test = routeTest ∨ test = auditTest := by
  simp [Protocol.fiber, ProbeCatalog.spectralTests, NativeExperiments.protocol,
    profile, instrument, pair, TimedPair.left, TimedPair.right, routeTest, auditTest, eq_comm]

private theorem legal {x y : ℚ} (hx : |x| ≤ 1/2) (hy : |y| ≤ 1/2)
    (hxy : x = 0 ∨ y = 1/4) : D.legal profile (law x y) := by
  refine ⟨Example.disclosed.legal.1, True.intro, ⟨?_, ?_, Example.disclosed.legal.2.2.2.2.1, rfl⟩⟩
  · refine ⟨fun _ => by norm_num [D, NativeExperiments.protocol, instrument, law],
      by norm_num [law, Fin.sum_univ_succ], ?_⟩
    intro r hr
    change r ∈ D.checks.rateTests {()} {()} at hr
    have he : r = ⟨routeRateRow [0, 1] [0, 2], 1⟩ := by
      simpa [ProbeCatalog.rateTests, NativeExperiments.protocol, instrument, pair,
        TimedPair.left, TimedPair.right] using hr
    subst r
    apply (route_rate_compile _ _ _ 1).mpr
    norm_num [law]
  · refine ⟨?_, ?_⟩
    · intro r hr
      rcases (test_mem r).mp hr with ⟨i, rfl⟩ | rfl | rfl
      · cases i
        simp [MonomialTest.holds, reversalTest]
      · let a (m : Mark) (i : Unit) := spectrum x y (m,i)
        change monomial (characterExponent [0, 1] ()) (fun p => a p.1 p.2) =
          1 * monomial (characterExponent [0, 2] ()) (fun p => a p.1 p.2)
        rw [character_monomial [0, 1] () a, character_monomial [0, 2] () a, one_mul]
        rcases hxy with rfl | rfl <;> simp [a, spectrum]
      · change monomial (pointExponent auditIndex) (spectrum x y) =
          (1/4) * monomial (fun _ => 0) (spectrum x y)
        rw [pointMonomial]
        norm_num [monomial, spectrum, auditIndex]
    · intro b hb
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hb
      change (∑ i : Unit, |spectrum x y (m,i)|) ≤ 1/2
      simp only [Fintype.sum_unique]
      fin_cases m <;> norm_num [spectrum] <;> assumption

noncomputable def state (x y : ℚ) (hx : |x| ≤ 1/2) (hy : |y| ≤ 1/2)
    (hxy : x = 0 ∨ y = 1/4) : State :=
  ⟨profile, law x y, legal hx hy hxy⟩

noncomputable def initial : State :=
  state (1/4) (1/4) (by norm_num) (by norm_num) (Or.inr rfl)

noncomputable def released : State :=
  state 0 (1/4) (by norm_num) (by norm_num) (Or.inl rfl)

noncomputable def throughZero : State :=
  state 0 0 (by norm_num) (by norm_num) (Or.inl rfl)

noncomputable def target : State :=
  state 0 (-1/4) (by norm_num) (by norm_num) (Or.inl rfl)

theorem route_equation (s : State) (hs : s.profile = profile) :
    s.law.spectrum gateIndex * s.law.spectrum responseIndex =
      s.law.spectrum gateIndex * s.law.spectrum auditIndex := by
  have hg : () ∈ s.profile.licenses := by rw [hs]; simp [profile]
  have h := (instrument.license_measured s hg).2
  have hword := (instrument.parity.word_identity_iff (fun m i => s.law.spectrum (m,i))
    (0 : Mark) 0 [1] [2]).mp h ()
  simpa [gateIndex, responseIndex, auditIndex] using hword

theorem pins_response (s : State) (hs : s.profile = profile)
    (hx : s.law.spectrum gateIndex ≠ 0) :
    s.law.spectrum responseIndex = 1/4 := by
  have ha : () ∈ s.profile.published := by rw [hs]; simp [profile]
  have hz : s.law.spectrum auditIndex = 1/4 :=
    instrument.calibration_value s ha (m := 2) (i := ()) (c := 1/4) rfl
  exact mul_left_cancel₀ hx ((route_equation s hs).trans (congrArg (_ * ·) hz))

theorem held_trajectories (s : State) (hs : s.profile = profile) (a : Bool × Cell) (b : Bool) :
    nativeWordEndpoint (s.law.marked instrument.parity) [0, 1] a b =
      nativeWordEndpoint (s.law.marked instrument.parity) [0, 2] a b := by
  have hg : () ∈ s.profile.licenses := by rw [hs]; simp [profile]
  exact instrument.licensed_trajectory_test s hg a b

/-- The permitted path changes only the spectrum, at one fixed held profile. -/
def axisPinned (freeResponse : Bool) (s : State) : Prop :=
  if freeResponse then s.law.spectrum gateIndex = 0
  else s.law.spectrum responseIndex = 1/4

abbrev RewriteStep (ε : ℚ) (freeResponse : Bool) (s t : State) : Prop :=
  s.profile = profile ∧ t.profile = profile ∧ D.Step ε .rewrite s t ∧
    axisPinned freeResponse s ∧ axisPinned freeResponse t ∧
    s.law.rate = t.law.rate ∧ s.law.register = t.law.register

abbrev RewriteChain (ε : ℚ) (freeResponse : Bool) :=
  Relation.ReflTransGen (RewriteStep ε freeResponse)

private theorem near {x y x' y' ε : ℚ}
    (hx : |x - x'| < ε) (hy : |y - y'| < ε) :
    PhysicalNear instrument.parity ε (law x y) (law x' y') := by
  rintro m ⟨a,u⟩ ⟨b,v⟩
  let L := Example.table true m a b u v
  let F := instrument.parity.kernel (fun i => spectrum x y (m,i)) a b
  let G := instrument.parity.kernel (fun i => spectrum x' y' (m,i)) a b
  have htable := Example.disclosed.legal.2.2.2.2.1
  have hL : |L| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ L from htable.1 m a b u v)]
    exact htable.entry_le_one m a b u v
  have hk : |F - G| < ε := by
    have h (i : Unit) : |spectrum x y (m,i) - spectrum x' y' (m,i)| ≤
        max |x - x'| |y - y'| := by
      have hzero : 0 ≤ max |x - x'| |y - y'| := (abs_nonneg _).trans (le_max_left _ _)
      fin_cases m
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simpa only [spectrum, sub_self, abs_zero] using hzero
      · simpa only [spectrum, sub_self, abs_zero] using hzero
    have hb := instrument.parity.kernel_sub_le h a b
    exact (by simpa using hb : |F - G| ≤ max |x - x'| |y - y'|).trans_lt (max_lt hx hy)
  change |(1/4 : ℚ) * F * L - (1/4) * G * L| < ε
  rw [show (1/4 : ℚ) * F * L - (1/4) * G * L = ((1/4) * (F - G)) * L by ring,
    abs_mul, abs_mul]
  have hb : |(1/4 : ℚ)| * |F - G| ≤ |F - G| :=
    mul_le_of_le_one_left (abs_nonneg _) (by norm_num)
  exact ((mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hL).trans hb).trans_lt hk

/-- The first axis changes the gate while the response is pinned.
The second changes the response with the gate identically zero. -/
noncomputable def axis (freeResponse : Bool) (v : ℚ) (hv : |v| ≤ 1/2) : State :=
  if freeResponse then state 0 v (by norm_num) hv (Or.inl rfl)
  else state v (1/4) hv (by norm_num) (Or.inr rfl)

private theorem axis_profile (freeResponse : Bool) (v : ℚ) (hv : |v| ≤ 1/2) :
    (axis freeResponse v hv).profile = profile := by
  cases freeResponse <;> rfl

private theorem axis_step (freeResponse : Bool) {a b ε : ℚ} (ha : |a| ≤ 1/2)
    (hb : |b| ≤ 1/2) (hε : 0 < ε) (hab : |a-b| < ε) :
    RewriteStep ε freeResponse (axis freeResponse a ha) (axis freeResponse b hb) := by
  refine ⟨axis_profile _ _ _, axis_profile _ _ _, ?_⟩
  cases freeResponse
  · exact ⟨⟨rfl, near hab (by simpa using hε)⟩, rfl, rfl, rfl, rfl⟩
  · exact ⟨⟨rfl, near (by simpa using hε) hab⟩, rfl, rfl, rfl, rfl⟩

private theorem axis_chain (freeResponse : Bool) {a b ε : ℚ} (ha : |a| ≤ 1/2)
    (hb : |b| ≤ 1/2) (hε : 0 < ε) :
    RewriteChain ε freeResponse (axis freeResponse a ha) (axis freeResponse b hb) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|a-b| / ε)
  let N : ℕ := n+1
  have hN : 0 < (N : ℚ) := by exact_mod_cast Nat.succ_pos n
  have hnN : (n : ℚ) < (N : ℚ) := by exact_mod_cast Nat.lt_succ_self n
  let t (k : ℕ) : ℚ := k / (N : ℚ)
  let v (k : ℕ) : ℚ := (1 - t k)*a + t k*b
  have bound (k : ℕ) (hk : k ≤ N) : |v k| ≤ 1/2 := by
    have ht₀ : 0 ≤ t k := div_nonneg (by positivity) hN.le
    have ht₁ : t k ≤ 1 := (div_le_iff₀ hN).2 (by simpa using (show (k : ℚ) ≤ N by exact_mod_cast hk))
    have H := abs_add_le ((1-t k)*a) (t k*b)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht₁), abs_mul, abs_of_nonneg ht₀] at H
    apply H.trans
    calc
      _ ≤ (1 - t k)*(1/2) + t k*(1/2) := by
        gcongr
        linarith
      _ = _ := by ring
  have mesh (k : ℕ) : |v k - v (k+1)| < ε := by
    have hd : v k - v (k+1) = (a - b) / (N : ℚ) := by
      simp only [v, t, Nat.cast_add, Nat.cast_one]
      ring
    rw [hd, abs_div, abs_of_pos hN]
    apply (div_lt_iff₀ hN).2
    exact (div_lt_iff₀ hε).1 (hn.trans hnN) |>.trans_eq (mul_comm _ _)
  have build (k : ℕ) (hk : k ≤ N) :
      RewriteChain ε freeResponse (axis freeResponse (v 0) (bound 0 (Nat.zero_le N)))
        (axis freeResponse (v k) (bound k hk)) := by
    induction k with
    | zero => exact .refl
    | succ k ih =>
      have hk' := (Nat.le_succ k).trans hk
      exact (ih hk').tail (axis_step freeResponse (bound k hk') (bound (k+1) hk) hε (mesh k))
  have hstart : v 0 = a := by simp [v, t]
  have hend : v N = b := by simp [v, t, hN.ne']
  simpa only [hstart, hend] using build N le_rfl

theorem edits_through_zero {ε : ℚ} (hε : 0 < ε) :
    RewriteChain ε false initial released ∧ RewriteChain ε true released throughZero ∧
      RewriteChain ε true throughZero target :=
  ⟨axis_chain false (by norm_num) (by norm_num) hε,
   axis_chain true (by norm_num) (by norm_num) hε,
   axis_chain true (by norm_num) (by norm_num) hε⟩

theorem factorable : D.Factorable initial target := by
  intro ε hε
  obtain ⟨h₁,h₂,h₃⟩ := edits_through_zero hε
  have lift (freeResponse : Bool) {s t : State} (h : RewriteChain ε freeResponse s t) :
      D.Chain ε s t := h.lift id fun _ _ hstep => ⟨.rewrite, hstep.2.2.1⟩
  exact (lift false h₁).trans ((lift true h₂).trans (lift true h₃))

/-- Actual one-step projected probabilities of retaining the false parity bit. -/
theorem projected_response (s : State) (u : Cell) :
    (∑ v, s.law.marked instrument.parity 1 (false,u) (false,v)) =
      s.law.rate 1 * ((1 + s.law.spectrum responseIndex) / 2) := by
  have h := native_projection instrument.parity (fun m i => s.law.spectrum (m,i))
    s.law.rate s.law.register 1 false false u (s.legal.2.2.2.2.1.2.1 1 false false u)
  simpa [PhysicalLaw.marked, ParityBasis.kernel, instrument, Example.parity, responseIndex]
    using h

theorem projected_response_endpoints (u : Cell) :
    (∑ v, initial.law.marked instrument.parity 1 (false,u) (false,v)) = 5/32 ∧
      (∑ v, target.law.marked instrument.parity 1 (false,u) (false,v)) = 3/32 := by
  rw [projected_response, projected_response]
  norm_num [initial, target, state, law, spectrum, responseIndex]

noncomputable def rows : List (ExponentRow Index) :=
  (D.fiber profile).spectralChecks.map MonomialTest.row

def initialSupport : Finset Index := {gateIndex, responseIndex, auditIndex}
def releasedSupport : Finset Index := {responseIndex, auditIndex}
def coreSupport : Finset Index := {auditIndex}

noncomputable def code (s : State) : Index → SignType := signCode (embed s.law.spectrum)

private theorem support_initial : codeSupport (code initial) = initialSupport := by
  rw [code, codeSupport_signCode]
  ext ⟨m,i⟩
  cases i
  fin_cases m <;> norm_num [mem_realSupport, embed, initial, state, law, spectrum,
    initialSupport, gateIndex, responseIndex, auditIndex] <;> decide

private theorem support_released : codeSupport (code released) = releasedSupport := by
  rw [code, codeSupport_signCode]
  ext ⟨m,i⟩
  cases i
  fin_cases m <;> norm_num [mem_realSupport, embed, released, state, law, spectrum,
    releasedSupport, responseIndex, auditIndex] <;> decide

private theorem support_target : codeSupport (code target) = releasedSupport := by
  rw [code, codeSupport_signCode]
  ext ⟨m,i⟩
  cases i
  fin_cases m <;> norm_num [mem_realSupport, embed, target, state, law, spectrum,
    releasedSupport, responseIndex, auditIndex] <;> decide

private theorem support_throughZero : codeSupport (code throughZero) = coreSupport := by
  rw [code, codeSupport_signCode]
  ext ⟨m,i⟩
  cases i
  fin_cases m <;> norm_num [mem_realSupport, embed, throughZero, state, law, spectrum,
    coreSupport, auditIndex] <;> decide

private theorem route_row_mem : routeTest.row ∈ rows :=
  List.mem_map.mpr ⟨routeTest, (test_mem _).2 (Or.inr (Or.inl rfl)), rfl⟩

private theorem audit_row_mem : auditTest.row ∈ rows :=
  List.mem_map.mpr ⟨auditTest, (test_mem _).2 (Or.inr (Or.inr rfl)), rfl⟩

private theorem route_balance (w : Index → ℕ) :
    (∑ i, routeTest.row.lhs i * w i) = (∑ i, routeTest.row.rhs i * w i) ↔
      w responseIndex = w auditIndex := by
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fin.sum_univ_succ]
  change 1 * w gateIndex + (1 * w responseIndex + (0 * w auditIndex + (0 * w (3,()) + 0))) =
    1 * w gateIndex + (0 * w responseIndex + (1 * w auditIndex + (0 * w (3,()) + 0))) ↔ _
  omega

private theorem audit_balance (w : Index → ℕ) :
    (∑ i, auditTest.row.lhs i * w i) = (∑ i, auditTest.row.rhs i * w i) ↔
      w auditIndex = 0 := by
  have h : (∑ i, pointExponent auditIndex i * w i) = w auditIndex := by
    simp [pointExponent]
  simpa [auditTest, calibrationTest] using (show
    (∑ i, pointExponent auditIndex i * w i) = 0 ↔ w auditIndex = 0 from by rw [h])

private theorem route_active_initial : routeTest.row.active initialSupport := by
  rintro ⟨m,i⟩ hm
  cases i
  fin_cases m
  · exact (hm (by decide)).elim
  · exact (hm (by decide)).elim
  · exact (hm (by decide)).elim
  · decide

private theorem audit_active {s : Finset Index} (ha : auditIndex ∈ s) :
    auditTest.row.active s := by
  intro i hi
  have hne : i ≠ auditIndex := fun h => hi (h ▸ ha)
  change pointExponent auditIndex i = 0 ∧ (0 : ℕ) = 0
  simp [pointExponent, hne]

private theorem route_inactive_without_gate {s : Finset Index} (hx : gateIndex ∉ s) :
    ¬ routeTest.row.active s := by
  intro h
  have hz := (h gateIndex hx).1
  change 1 = 0 at hz
  omega

theorem route_inactive_of_gate_zero (s : State) (hx : s.law.spectrum gateIndex = 0) :
    ¬ routeTest.row.active (codeSupport (code s)) := by
  apply route_inactive_without_gate
  rw [code, codeSupport_signCode, mem_realSupport, embed, hx]
  simp

theorem route_inactive_released : ¬ routeTest.row.active releasedSupport := by
  rw [← support_released]
  exact route_inactive_of_gate_zero released rfl

private theorem keeps_audit_weight {s : Finset Index} {w : Index → ℕ}
    (hw : Damping rows s w) (h : auditIndex ∈ s) : w auditIndex = 0 :=
  (audit_balance w).mp (hw.2 _ audit_row_mem (audit_active h))

private theorem keeps_initial_response_weight {w : Index → ℕ}
    (hw : Damping rows initialSupport w) : w responseIndex = 0 :=
  ((route_balance w).mp (hw.2 _ route_row_mem route_active_initial)).trans
    (keeps_audit_weight hw (by decide))

private def kill (index i : Index) : ℕ := if i = index then 1 else 0

private theorem kill_outside {s : Finset Index} {i : Index} (hi : i ∈ s) :
    ∀ j ∉ s, kill i j = 0 := by
  intro j hj
  have hne : j ≠ i := fun h => hj (h ▸ hi)
  simp [kill, hne]

theorem first_contraction : Contracts rows initialSupport releasedSupport := by
  refine ⟨kill gateIndex, ⟨kill_outside (by decide), ?_⟩, by decide⟩
  intro r hr _
  obtain ⟨test, ht, rfl⟩ := List.mem_map.mp hr
  rcases (test_mem test).mp ht with ⟨i, rfl⟩ | rfl | rfl
  · cases i
    rfl
  · exact (route_balance _).mpr (by decide)
  · exact (audit_balance _).mpr (by decide)

theorem second_contraction : Contracts rows releasedSupport coreSupport := by
  refine ⟨kill responseIndex, ⟨kill_outside (by decide), ?_⟩, by decide⟩
  intro r hr ha
  obtain ⟨test, ht, rfl⟩ := List.mem_map.mp hr
  rcases (test_mem test).mp ht with ⟨i, rfl⟩ | rfl | rfl
  · cases i
    rfl
  · exact (route_inactive_released ha).elim
  · exact (audit_balance _).mpr (by decide)

theorem two_contractions :
    Contracts rows (codeSupport (code initial)) (codeSupport (code released)) ∧
      Contracts rows (codeSupport (code released)) (codeSupport (code throughZero)) := by
  rw [support_initial, support_released, support_throughZero]
  exact ⟨first_contraction, second_contraction⟩

theorem no_single_contraction_to_core : ¬ Contracts rows initialSupport coreSupport := by
  rintro ⟨w, hw, ht⟩
  have hy : responseIndex ∈ coreSupport := by
    rw [ht, Finset.mem_filter]
    exact ⟨by decide, keeps_initial_response_weight hw⟩
  exact (by decide : responseIndex ∉ coreSupport) hy

private theorem initial_response_sign : code initial responseIndex = 1 := by
  apply sign_pos
  norm_num [embed, initial, state, law, spectrum, responseIndex]

private theorem target_response_sign : code target responseIndex = -1 := by
  apply sign_neg
  norm_num [embed, target, state, law, spectrum, responseIndex]

theorem no_single_contraction_to_target_sign :
    ¬ ∃ w, Damping rows (codeSupport (code initial)) w ∧
      code target = fun i => if w i = 0 then code initial i else 0 := by
  rintro ⟨w, hw, hcode⟩
  rw [support_initial] at hw
  have h := congrFun hcode responseIndex
  rw [keeps_initial_response_weight hw, if_pos rfl, initial_response_sign, target_response_sign] at h
  exact (by decide : (-1 : SignType) ≠ 1) h

private theorem retains_audit {s t : Finset Index} (h : Reduces rows s t)
    (ha : auditIndex ∈ s) : auditIndex ∈ t := by
  induction h with
  | refl => exact ha
  | tail _ step ih =>
    obtain ⟨w, hw, rfl⟩ := step
    exact Finset.mem_filter.mpr ⟨ih, keeps_audit_weight hw ih⟩

private theorem exact_core {s : Finset Index} (h : Reduces rows s coreSupport)
    (ha : auditIndex ∈ s) : core rows s = coreSupport := by
  refine (isCore_core rows s).unique ⟨h, ?_⟩
  intro t ht
  exact Finset.singleton_subset_iff.mpr (retains_audit ht ha)

/-- Both endpoints retain exactly the positive calibrated response in the signed core. -/
theorem signed_cores :
    signedCore rows (code initial) = (fun i => if i = auditIndex then 1 else 0) ∧
      signedCore rows (code target) = (fun i => if i = auditIndex then 1 else 0) := by
  have h₁ := exact_core (.tail (.single first_contraction) second_contraction) (by decide)
  have h₂ := exact_core (.single second_contraction) (by decide)
  constructor <;> funext i
  · unfold signedCore
    rw [support_initial, h₁]
    by_cases h : i = auditIndex
    · subst i
      simp only [coreSupport, Finset.mem_singleton]
      apply sign_pos
      norm_num [embed, initial, state, law, spectrum, auditIndex]
    · simp [coreSupport, h]
  · unfold signedCore
    rw [support_target, h₂]
    by_cases h : i = auditIndex
    · subst i
      simp only [coreSupport, Finset.mem_singleton]
      apply sign_pos
      norm_num [embed, target, state, law, spectrum, auditIndex]
    · simp [coreSupport, h]

/-- The general theorem already predicts the connection from the computed core. -/
theorem factorable_by_signed_core : D.Factorable initial target := by
  obtain ⟨hi, ht⟩ := signed_cores
  apply (instrument.exact_six_iff initial target).mpr
  exact ⟨le_refl _, hi.trans ht.symm⟩

/-- Freeze the activation test at the initial support, while contracting only
coordinates in the current support. -/
def FrozenContracts (s t : Finset Index) : Prop :=
  ∃ w : Index → ℕ, Damping rows initialSupport w ∧
    (∀ i ∉ s, w i = 0) ∧ t = s.filter (fun i => w i = 0)

def FrozenReduct (a b : Index → SignType) : Prop :=
  Relation.ReflTransGen FrozenContracts (codeSupport a) (codeSupport b) ∧
    ∀ i ∈ codeSupport b, b i = a i

private theorem frozen_retains_response {s t : Finset Index}
    (h : Relation.ReflTransGen FrozenContracts s t) (hy : responseIndex ∈ s) :
    responseIndex ∈ t := by
  induction h with
  | refl => exact hy
  | tail _ step ih =>
    obtain ⟨w, hw, _, rfl⟩ := step
    exact Finset.mem_filter.mpr ⟨ih, keeps_initial_response_weight hw⟩

/-- The frozen equations wrongly put the connected endpoints in different
classes, since their opposite response signs survive every frozen reduction. -/
theorem frozen_rejects :
    ¬ ∃ b, FrozenReduct (code initial) b ∧ FrozenReduct (code target) b := by
  rintro ⟨b, hi, ht⟩
  have hy := frozen_retains_response hi.1 (by rw [support_initial]; decide)
  have h := (hi.2 responseIndex hy).symm.trans (ht.2 responseIndex hy)
  rw [initial_response_sign, target_response_sign] at h
  exact (by decide : (1 : SignType) ≠ -1) h

theorem fixed_audit_signal (s : State) (hs : s.profile = profile) (a : Bool × Cell) :
    observedSignal instrument.parity (s.law.marked instrument.parity) 2 a () =
      s.law.rate 2 * (1/4) := by
  have ha : () ∈ s.profile.published := by rw [hs]; simp [profile]
  exact instrument.published_calibration s ha rfl a

/-- Spectral support changes without deleting any native transition. -/
theorem physical_support_held (s t : State) (hs : s.profile = profile) (ht : t.profile = profile)
    (m : Mark) (x y : Bool) (u v : Cell) :
    0 < s.law.marked instrument.parity m (x,u) (y,v) ↔
      0 < t.law.marked instrument.parity m (x,u) (y,v) := by
  rw [instrument.physical_support, instrument.physical_support, hs, ht]

end MovingProjection.StagedContraction
