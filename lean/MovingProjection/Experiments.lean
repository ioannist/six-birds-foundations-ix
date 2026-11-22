import MovingProjection.ExactSix

/-!
An audited protocol built from timed route experiments and measured
calibrations. The catalogue is generated from the experiments.
-/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I]

structure TimedPair (M : Type*) (H : ℕ) where
  first : M
  next : M
  tail : List M
  other : List M
  duration : tail.length = other.length
  fits : tail.length + 1 ≤ H

def TimedPair.left {H : ℕ} (p : TimedPair M H) : List M := p.first :: p.tail
def TimedPair.right {H : ℕ} (p : TimedPair M H) : List M := p.next :: p.other

inductive AuditQuery (M I : Type*) (H : ℕ)
  | ratio (pair : TimedPair M H) (value : ℚ) (positive : 0 < value)
  | calibration (mark : M) (probe : I) (value : ℚ)

def pointExponent {T : Type*} [DecidableEq T] (i j : T) : ℕ :=
  if j = i then 1 else 0

theorem pointMonomial {T : Type*} [Fintype T] [DecidableEq T]
    (i : T) (x : T → ℚ) : monomial (pointExponent i) x = x i := by
  simp [monomial, pointExponent]

def calibrationTest (m : M) (i : I) (c : ℚ) : MonomialTest (M × I) :=
  ⟨⟨pointExponent (m,i), fun _ => 0⟩,c⟩

def reversalTest (rev : M → M) (p : M × I) : MonomialTest (M × I) :=
  ⟨⟨pointExponent p, pointExponent (rev p.1,p.2)⟩,1⟩

structure NativeExperiments (M I X R Γ Δ : Type*) [Fintype X] [Fintype R] [DecidableEq I] where
  parity : ParityBasis I X
  weights : R → ℚ
  weights_pos : ∀ r, 0 < weights r
  weights_unit : ∑ r, weights r = 1
  reversal : M → M
  reversal_involutive : Function.Involutive reversal
  δ : ℚ
  κ : ℚ
  δ_pos : 0 < δ
  κ_lt_one : κ < 1
  horizon : ℕ
  license : Γ → TimedPair M horizon
  audit : Δ → AuditQuery M I horizon
  policy : Finset Γ → Prop

namespace NativeExperiments

noncomputable def protocol (D : NativeExperiments M I X R Γ Δ) : Protocol M I X R Γ Δ where
  kernel := D.parity
  ν := D.weights
  reverse := D.reversal
  δ := D.δ
  κ := D.κ
  δ_pos := D.δ_pos
  κ_lt_one := D.κ_lt_one
  checks := {
    licenseRate := fun g =>
      [⟨routeRateRow (D.license g).left (D.license g).right,1⟩]
    licenseSpectrum := fun g => Finset.univ.toList.map
      (routeCharacterTest (D.license g).left (D.license g).right)
    auditRate := fun e => match D.audit e with
      | .ratio pair c _ => [⟨routeRateRow pair.left pair.right,c⟩]
      | .calibration _ _ _ => []
    auditSpectrum := fun e => match D.audit e with
      | .ratio _ _ _ => []
      | .calibration m i c => [calibrationTest m i c]
    reversal := Finset.univ.toList.map (reversalTest D.reversal)
    licensePolicy := D.policy
  }

theorem reversal_holds (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (s : D.protocol.State n) (m : M) (i : I) :
    s.law.spectrum (m,i) = s.law.spectrum (D.reversal m,i) := by
  have ht : reversalTest D.reversal (m,i) ∈ (D.protocol.fiber s.profile).spectralChecks := by
    simp [Protocol.fiber, ProbeCatalog.spectralTests, protocol]
  have hh := s.legal.2.2.2.1.1 _ ht
  simpa [MonomialTest.holds, reversalTest, pointMonomial] using hh

theorem license_measured (D : NativeExperiments M I X R Γ Δ) [Nonempty X] {n : ℕ}
    (s : D.protocol.State n) {g : Γ} (hg : g ∈ s.profile.licenses) :
    ((D.license g).left.map s.law.rate).prod = ((D.license g).right.map s.law.rate).prod ∧
    D.parity.nonemptyWord (fun m i => s.law.spectrum (m,i)) (D.license g).first (D.license g).tail =
    D.parity.nonemptyWord (fun m i => s.law.spectrum (m,i)) (D.license g).next (D.license g).other := by
  constructor
  · have hr : (⟨routeRateRow (D.license g).left (D.license g).right,1⟩ : MonomialTest M) ∈
        (D.protocol.fiber s.profile).rateChecks := by
      unfold Protocol.fiber ProbeCatalog.rateTests
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, Finset.mem_toList.mpr hg, by
        simp [protocol]⟩)
    have h := (route_rate_compile _ _ _ 1).mp (s.legal.2.2.1.2.2 _ hr)
    simpa using h
  · apply (route_character_compile D.parity _ _ _ _ _).mpr
    intro i
    have ht : routeCharacterTest (D.license g).left (D.license g).right i ∈
        (D.protocol.fiber s.profile).spectralChecks := by
      unfold Protocol.fiber ProbeCatalog.spectralTests
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨g,Finset.mem_toList.mpr hg, by simp [protocol]⟩))
    change (routeCharacterTest (D.license g).left (D.license g).right i).holds s.law.spectrum
    exact s.legal.2.2.2.1.1 _ ht

omit [Fintype M] [Fintype I] [DecidableEq M] in
theorem licensed_duration (D : NativeExperiments M I X R Γ Δ) (g : Γ) :
    (D.license g).left.length = (D.license g).right.length := by
  simpa [TimedPair.left, TimedPair.right] using (D.license g).duration

theorem calibration_value (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (s : D.protocol.State n) {e : Δ} (he : e ∈ s.profile.published)
    {m : M} {i : I} {c : ℚ} (hquery : D.audit e = .calibration m i c) :
    s.law.spectrum (m,i) = c := by
  have ht : calibrationTest m i c ∈ (D.protocol.fiber s.profile).spectralChecks := by
    unfold Protocol.fiber ProbeCatalog.spectralTests
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,Finset.mem_toList.mpr he, by
      simp [protocol, hquery]⟩)
  have h := s.legal.2.2.2.1.1 _ ht
  change monomial (pointExponent (m,i)) s.law.spectrum =
    c * monomial (fun _ => 0) s.law.spectrum at h
  rw [pointMonomial] at h
  simpa [monomial] using h

theorem published_calibration (D : NativeExperiments M I X R Γ Δ) [Nonempty X] {n : ℕ}
    (s : D.protocol.State n) {e : Δ} (he : e ∈ s.profile.published)
    {m : M} {i : I} {c : ℚ} (hquery : D.audit e = .calibration m i c)
    (x : X × R) :
    observedSignal D.parity (s.law.marked D.parity) m x i = s.law.rate m * c := by
  change observedSignal D.parity (nativeMarked D.parity (fun m i => s.law.spectrum (m,i))
    s.law.rate s.law.register) m x i = _
  rw [observedSignal_native _ _ _ _ s.legal.2.2.2.2.1.2.1, D.calibration_value s he hquery]

theorem audited_pair (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (s : D.protocol.State n) (m : M) (x y : X × R) :
    nativeStationary D.weights x * s.law.marked D.parity m x y * s.law.rate (D.reversal m) =
      nativeStationary D.weights y * s.law.marked D.parity (D.reversal m) y x * s.law.rate m := by
  apply native_reverse _ _ _ _ _ _ _ _ _
  · funext i
    exact D.reversal_holds s m i
  · exact s.legal.2.2.2.2.1.2.2.2.1 m x.1 y.1 x.2 y.2

private theorem word_degree (w : List M) : (∑ m, w.count m) = w.length := by
  rw [← List.sum_toFinset_count_eq_length]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m _ hm
  exact List.count_eq_zero.mpr (fun hx => hm (List.mem_toFinset.mpr hx))

private theorem same_degree {H : ℕ} (p : TimedPair M H) :
    (∑ m, (routeRateRow p.left p.right).lhs m) =
      ∑ m, (routeRateRow p.left p.right).rhs m := by
  change (∑ m, p.left.count m) = ∑ m, p.right.count m
  rw [word_degree, word_degree]
  simpa [TimedPair.left, TimedPair.right] using p.duration

theorem compiled_rate_tests (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (p : Capabilities M X R Γ Δ n) :
    ∀ r ∈ (D.protocol.fiber p).rateChecks,
      ((∑ m, r.row.lhs m) = ∑ m, r.row.rhs m) ∧ 0 < r.ratio := by
  intro r hr
  change r ∈ D.protocol.checks.rateTests p.licenses p.published at hr
  simp only [ProbeCatalog.rateTests, List.mem_append, List.mem_flatMap] at hr
  rcases hr with ⟨g, _, hg⟩ | ⟨e, _, he⟩
  · change r ∈ [⟨routeRateRow (D.license g).left (D.license g).right,1⟩] at hg
    obtain rfl := List.mem_singleton.mp hg
    exact ⟨same_degree _, zero_lt_one⟩
  · change r ∈ (match D.audit e with
        | .ratio pair c _ => [({ row := routeRateRow pair.left pair.right, ratio := c } :
          MonomialTest M)]
        | .calibration _ _ _ => []) at he
    cases hquery : D.audit e with
    | ratio pair c hp =>
      rw [hquery] at he
      obtain rfl := List.mem_singleton.mp he
      exact ⟨same_degree _, hp⟩
    | calibration =>
      rw [hquery] at he
      cases he

theorem exact_six_iff (D : NativeExperiments M I X R Γ Δ) [Nonempty M] [Nonempty X] [Nonempty R]
    [Fintype Γ] [Fintype Δ] {n : ℕ} (a b : D.protocol.State n) :
    D.protocol.Factorable a b ↔ a.profile ≤ b.profile ∧
      D.protocol.signature a.profile a.law = D.protocol.signature a.profile b.law :=
  D.protocol.factorable_iff a b
    (fun r hr => (D.compiled_rate_tests a.profile r hr).1)
    (fun r hr => (D.compiled_rate_tests a.profile r hr).2)

theorem measured_law_injective (D : NativeExperiments M I X R Γ Δ)
    [Nonempty X] [Nonempty R] {n : ℕ} {a b : D.protocol.State n}
    (h : a.law.marked D.parity = b.law.marked D.parity) : a.law = b.law := by
  let s : X × R := Classical.choice inferInstance
  have hra := a.legal.2.2.2.2.1.2.1
  have hrb := b.legal.2.2.2.2.1.2.1
  have hθ : a.law.rate = b.law.rate := by
    funext m
    have he := congrArg (fun P => observedRate P m s) h
    exact (observedRate_native _ _ _ _ hra m s).symm.trans
      (he.trans (observedRate_native _ _ _ _ hrb m s))
  have hs : a.law.spectrum = b.law.spectrum := by
    funext mi
    rcases mi with ⟨m,i⟩
    have ho := congrArg (fun P => observedSignal D.parity P m s i) h
    have he : a.law.rate m * a.law.spectrum (m,i) = b.law.rate m * b.law.spectrum (m,i) :=
      (observedSignal_native _ _ _ _ hra m s i).symm.trans
        (ho.trans (observedSignal_native _ _ _ _ hrb m s i))
    rw [← hθ] at he
    exact mul_left_cancel₀ (D.δ_pos.trans_le (a.legal.2.2.1.1 m)).ne' he
  have hL : a.law.register = b.law.register := by
    funext m x y u v
    have ho := congrFun (congrFun (congrFun h m) (x,u)) (y,v)
    change (a.law.rate m * D.parity.kernel (fun i => a.law.spectrum (m,i)) x y) *
        a.law.register m x y u v =
      (b.law.rate m * D.parity.kernel (fun i => b.law.spectrum (m,i)) x y) *
        b.law.register m x y u v at ho
    rw [← hθ, ← hs] at ho
    exact mul_left_cancel₀
      (mul_pos (D.δ_pos.trans_le (a.legal.2.2.1.1 m))
        (D.parity.kernel_pos _ ((spectrum_budget a.legal.2.2.2.1 m).trans_lt D.κ_lt_one) x y)).ne' ho
  exact PhysicalLaw.ext hθ hs hL

theorem physical_support (D : NativeExperiments M I X R Γ Δ) [Nonempty X] {n : ℕ}
    (s : D.protocol.State n) (m : M) (x y : X) (u v : R) :
    0 < s.law.marked D.parity m (x,u) (y,v) ↔
      (m,x,y,u,v) ∈ s.profile.mask.ofDual := by
  have hq := D.parity.kernel_pos (fun i => s.law.spectrum (m,i))
    ((spectrum_budget s.legal.2.2.2.1 m).trans_lt D.κ_lt_one) x y
  have hθ := D.δ_pos.trans_le (s.legal.2.2.1.1 m)
  rw [← Protocol.legal_mask s.legal]
  change 0 < s.law.rate m * D.parity.kernel (fun i => s.law.spectrum (m,i)) x y *
      s.law.register m x y u v ↔ 0 < s.law.register m x y u v
  exact mul_pos_iff_of_pos_left (mul_pos hθ hq)

/-- Every disclosed decision has its prescribed conditional mass in the
prepared native experiment, at each held grade. -/
theorem disclosed_mass (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (s : D.protocol.State n) (j : Fin (n+1)) (m : M) (x y : X) (u : R)
    (d : R → Bool) (hd : Available (s.profile.grades j).ofDual d) :
    (∑ v, if d v then s.law.marked D.parity m (x,u) (y,v) else 0) =
      (∑ v, s.law.marked D.parity m (x,u) (y,v)) *
        (∑ v, if d v then D.weights v else 0) := by
  classical
  let a (m : M) (i : I) := s.law.spectrum (m,i)
  let P := nativeMarked D.parity a s.law.rate s.law.register
  have hreg := s.legal.2.2.2.2.1.coarsen (s.legal.1 (Fin.le_last j))
  have hmass := hreg.2.2.2.2 m x y u d hd
  change (∑ v, if d v then P m (x,u) (y,v) else 0) =
    (∑ v, P m (x,u) (y,v)) * (∑ v, if d v then D.weights v else 0)
  rw [← Finset.sum_filter, ← Finset.sum_filter] at hmass ⊢
  exact (native_block_test D.parity a _ _ m x y u _ _ hmass).trans
    (congrArg (fun v : ℚ => v * ∑ r ∈ Finset.univ.filter (fun r => d r = true), D.weights r)
      (native_projection D.parity a _ _ m x y u (hreg.2.1 m x y u)).symm)

theorem physical_stationarity (D : NativeExperiments M I X R Γ Δ) [Nonempty X] {n : ℕ}
    (s : D.protocol.State n) (y : X × R) :
    ∑ m, ∑ x, nativeStationary D.weights x * s.law.marked D.parity m x y =
      nativeStationary D.weights y :=
  native_stationarity _ _ _ _ _ s.legal.2.2.1.2.1 s.legal.2.2.2.2.1.2.2.1 y

theorem published_ratio (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (s : D.protocol.State n) {e : Δ} (he : e ∈ s.profile.published)
    {p : TimedPair M D.horizon} {c : ℚ} {hp : 0 < c} (hquery : D.audit e = .ratio p c hp) :
    (p.left.map s.law.rate).prod = c * (p.right.map s.law.rate).prod := by
  have ht : (⟨routeRateRow p.left p.right,c⟩ : MonomialTest M) ∈
      (D.protocol.fiber s.profile).rateChecks := by
    unfold Protocol.fiber ProbeCatalog.rateTests
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e,Finset.mem_toList.mpr he, by
      simp [protocol, hquery]⟩)
  exact (route_rate_compile _ _ _ _).mp (s.legal.2.2.1.2.2 _ ht)

/-- Native observation queries determine the semantic state of a presentation. -/
theorem state_of_readouts (D : NativeExperiments M I X R Γ Δ) [Nonempty X] [Nonempty R]
    {n : ℕ} {a b : D.protocol.State n}
    (capabilities : a.profile = b.profile)
    (trials : a.law.marked D.parity = b.law.marked D.parity) : a = b :=
  Protocol.State.ext capabilities (D.measured_law_injective trials)

theorem factorization_preserved_by_readouts (D : NativeExperiments M I X R Γ Δ)
    [Nonempty X] [Nonempty R] {A B : Type*} {n : ℕ}
    (realizeA : A → D.protocol.State n) (realizeB : B → D.protocol.State n)
    (translate : A ≃ B)
    (profile : ∀ a, (realizeA a).profile = (realizeB (translate a)).profile)
    (trials : ∀ a, (realizeA a).law.marked D.parity = (realizeB (translate a)).law.marked D.parity)
    (u v : A) :
    D.protocol.Factorable (realizeA u) (realizeA v) ↔
      D.protocol.Factorable (realizeB (translate u)) (realizeB (translate v)) := by
  rw [D.state_of_readouts (profile u) (trials u), D.state_of_readouts (profile v) (trials v)]

end NativeExperiments

end MovingProjection
