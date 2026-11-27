import MovingProjection.CoreOrder
import MovingProjection.Experiments

/-! The order properties for the measured single-word instrument. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I]

noncomputable abbrev Protocol.spectralRows (D : Protocol M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) : List (ExponentRow (M × I)) :=
  (D.fiber p).spectralChecks.map MonomialTest.row

omit [Fintype M] [Fintype I] [Fintype R] [DecidableEq M] in
theorem Protocol.spectralRows_mono (D : Protocol M I X R Γ Δ)
    {p q : Capabilities M X R Γ Δ n} (hpq : p ≤ q) :
    D.spectralRows p ⊆ D.spectralRows q := by
  have h := Capabilities.le_coordinates.mp hpq
  exact List.map_subset _ (D.checks.spectralTests_mono h.2.2.1 h.2.2.2)

omit [Fintype R] in
theorem Protocol.signature_eq_of_profile_le (D : Protocol M I X R Γ Δ)
    {p q : Capabilities M X R Γ Δ n} (hpq : p ≤ q) {a b : PhysicalLaw M I X R}
    (h : D.signature q a = D.signature q b) : D.signature p a = D.signature p b :=
  signedCore_eq_of_rows_subset (D.spectralRows_mono hpq) h

private theorem calibration_holds_iff (m : M) (i : I) (c : ℚ) (x : M × I → ℚ) :
    (calibrationTest m i c).holds x ↔ x (m,i) = c := by
  change monomial (pointExponent (m,i)) x = c * monomial (fun _ => 0) x ↔ _
  rw [pointMonomial]
  simp [monomial]

/-- A point-calibration row pins its coordinate whenever that coordinate is
present. The statement also applies to formal supports. -/
theorem calibration_mem_core {rows : List (ExponentRow (M × I))} {s : Finset (M × I)}
    {m : M} {i : I} {c : ℚ} (hr : (calibrationTest m i c).row ∈ rows)
    (hs : (m,i) ∈ s) : (m,i) ∈ core rows s := by
  have hsingle : ({(m,i)} : Finset (M × I)) ⊆ s := Finset.singleton_subset_iff.mpr hs
  have hfixed : core rows {(m,i)} = {(m,i)} := by
    apply core_eq_self_of_damping_zero
    intro w hw j hj
    obtain rfl := Finset.mem_singleton.mp hj
    have ha : (calibrationTest m i c).row.active {(m,i)} := by
      intro k hk
      simp [calibrationTest, pointExponent, show k ≠ (m,i) by simpa using hk]
    simpa [calibrationTest, pointExponent] using hw.2 _ hr ha
  apply core_mono_support rows hsingle
  rw [hfixed]
  exact Finset.mem_singleton_self _

namespace NativeExperiments

def NoNonzeroCalibration (D : NativeExperiments M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) : Prop :=
  ∀ e ∈ p.published, ∀ m i c, D.audit e = .calibration m i c → c = 0

private theorem character_degree (w : List M) (i : I) :
    (∑ mi : M × I, characterExponent w i mi) = ∑ m : M, w.count m := by
  simp [Fintype.sum_prod_type, characterExponent]

/-- Zero calibrations are inactive at passing spectra. Every active native
spectral row has equal total degrees when the profile has no nonzero calibration. -/
theorem active_spectral_rows_balanced (D : NativeExperiments M I X R Γ Δ)
    {p : Capabilities M X R Γ Δ n} {x : M × I → ℚ}
    (h : D.NoNonzeroCalibration p)
    (hx : ∀ t ∈ (D.protocol.fiber p).spectralChecks, t.holds x) :
    ∀ r ∈ D.protocol.spectralRows p, r.active (support x) →
      ∑ i, r.lhs i = ∑ i, r.rhs i := by
  intro row hr ha
  obtain ⟨test, htest, rfl⟩ := List.mem_map.mp hr
  have hholds := hx _ htest
  change test ∈ D.protocol.checks.spectralTests p.licenses p.published at htest
  simp only [ProbeCatalog.spectralTests, List.mem_append, List.mem_flatMap, Finset.mem_toList] at htest
  rcases htest with (hrev | ⟨g,hg,hroute⟩) | ⟨e,he,haudit⟩
  · change test ∈ Finset.univ.toList.map (reversalTest D.reversal) at hrev
    obtain ⟨mi,_,rfl⟩ := List.mem_map.mp hrev
    simp [reversalTest, pointExponent]
  · change test ∈ Finset.univ.toList.map
      (routeCharacterTest (D.license g).left (D.license g).right) at hroute
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hroute
    have hmem : (⟨routeRateRow (D.license g).left (D.license g).right,1⟩ :
        MonomialTest M) ∈ (D.protocol.fiber p).rateChecks := by
      unfold Protocol.fiber ProbeCatalog.rateTests
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨g, Finset.mem_toList.mpr hg,
        by simp [protocol]⟩)
    simpa only [routeCharacterTest, character_degree] using (D.compiled_rate_tests p _ hmem).1
  · change test ∈ (match D.audit e with
        | .ratio _ _ _ => [] | .calibration m i c => [calibrationTest m i c]) at haudit
    cases hq : D.audit e with
    | ratio =>
      rw [hq] at haudit
      cases haudit
    | calibration m i c =>
      rw [hq] at haudit
      obtain rfl := List.mem_singleton.mp haudit
      have hz : x (m,i) = 0 := ((calibration_holds_iff _ _ _ _).mp hholds).trans
        (h e he m i c hq)
      have hn : (m,i) ∉ support x := by simp [hz]
      have hf := (ha (m,i) hn).1
      simp [calibrationTest, pointExponent] at hf

/-- The anchor criterion is exact for every spectrum that passes the
profile's spectral tests, even if supplied at a later profile. -/
theorem spectral_core_empty_iff (D : NativeExperiments M I X R Γ Δ)
    {p : Capabilities M X R Γ Δ n} {x : M × I → ℚ}
    (hx : ∀ t ∈ (D.protocol.fiber p).spectralChecks, t.holds x) :
    core (D.protocol.spectralRows p) (support x) = ∅ ↔ D.NoNonzeroCalibration p := by
  constructor
  · intro h e he m i c hq
    have ht : calibrationTest m i c ∈ (D.protocol.fiber p).spectralChecks := by
      unfold Protocol.fiber ProbeCatalog.spectralTests
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, Finset.mem_toList.mpr he,
        by simp [protocol, hq]⟩)
    by_contra hc
    have hi : (m,i) ∈ support x :=
      mem_support.mpr (by rwa [(calibration_holds_iff _ _ _ _).mp (hx _ ht)])
    have hmem := calibration_mem_core (List.mem_map_of_mem ht) hi
    rw [show core (D.protocol.spectralRows p) (support x) = ∅ from h] at hmem
    exact Finset.notMem_empty _ hmem
  · exact fun h => core_eq_empty_of_balanced_active (D.active_spectral_rows_balanced h hx)

theorem signature_eq_zero_iff (D : NativeExperiments M I X R Γ Δ)
    {p : Capabilities M X R Γ Δ n} {a : PhysicalLaw M I X R}
    (ha : ∀ t ∈ (D.protocol.fiber p).spectralChecks, t.holds a.spectrum) :
    D.protocol.signature p a = 0 ↔ D.NoNonzeroCalibration p := by
  have hs : codeSupport (D.protocol.signature p a) =
      core (D.protocol.spectralRows p) (support a.spectrum) := by
    rw [Protocol.signature, codeSupport_signedCore, codeSupport_signCode,
      show realSupport (embed a.spectrum) = support a.spectrum from realSupport_cast _]
  rw [← D.spectral_core_empty_iff ha, ← hs]
  constructor
  · intro h
    rw [h]
    simp [codeSupport]
  · intro h
    funext i
    by_contra hi
    have hm : i ∈ codeSupport (D.protocol.signature p a) := by simpa [codeSupport] using hi
    simp [h] at hm

variable [Fintype Γ] [Fintype Δ] [Nonempty M] [Nonempty X] [Nonempty R]

theorem factorable_iff_profile_le_of_no_nonzero_calibration
    (D : NativeExperiments M I X R Γ Δ) (a b : D.protocol.State n)
    (hn : D.NoNonzeroCalibration a.profile) :
    D.protocol.Factorable a b ↔ a.profile ≤ b.profile := by
  rw [D.exact_six_iff]
  constructor
  · exact And.left
  · intro hab
    have h := Capabilities.le_coordinates.mp hab
    have hsubset := D.protocol.checks.spectralTests_mono h.2.2.1 h.2.2.2
    have ha := (D.signature_eq_zero_iff a.legal.2.2.2.1.1).2 hn
    have hb : D.protocol.signature a.profile b.law = 0 :=
      (D.signature_eq_zero_iff (p := a.profile) (a := b.law)
        (fun t ht => b.legal.2.2.2.1.1 t (hsubset ht))).2 hn
    exact ⟨hab, ha.trans hb.symm⟩

/-- Starting from a higher profile with the same spectrum can only remove
reachable targets. The other components of the two source laws may differ. -/
theorem factorable_of_higher_source (D : NativeExperiments M I X R Γ Δ)
    {a a' b : D.protocol.State n} (h : a.profile ≤ a'.profile)
    (hs : a.law.spectrum = a'.law.spectrum) (hf : D.protocol.Factorable a' b) :
    D.protocol.Factorable a b := by
  obtain ⟨hp, he⟩ := (D.exact_six_iff a' b).1 hf
  apply (D.exact_six_iff a b).2
  refine ⟨h.trans hp, ?_⟩
  have hh := D.protocol.signature_eq_of_profile_le h he
  simpa only [Protocol.signature, hs] using hh

/-- The greatest irreducible sub-support is realised by a mutually finely
reachable law at the same profile with the original rates, register and
surviving values. -/
theorem realise_core (D : NativeExperiments M I X R Γ Δ) (a : D.protocol.State n) :
    ∃ b : D.protocol.State n, b.profile = a.profile ∧ b.law.rate = a.law.rate ∧
      b.law.register = a.law.register ∧
      support b.law.spectrum = core (D.protocol.spectralRows a.profile) (support a.law.spectrum) ∧
      (∀ i ∈ support b.law.spectrum, b.law.spectrum i = a.law.spectrum i) ∧
      D.protocol.Factorable a b ∧ D.protocol.Factorable b a := by
  obtain ⟨x,hx,hf,hs,hval⟩ := fineConnected_to_core a.legal.2.2.2.1
  let b : D.protocol.State n := ⟨a.profile, ⟨a.law.rate,x,a.law.register⟩,
    a.legal.1,a.legal.2.1,a.legal.2.2.1,hx,a.legal.2.2.2.2⟩
  have hkey : D.protocol.signature a.profile a.law = D.protocol.signature a.profile b.law :=
    fineConnected_signedCore (bounded_of_budget_cover (spectrumBudgets_covers D.κ)) hf
  exact ⟨b,rfl,rfl,rfl,hs,hval,(D.exact_six_iff a b).2 ⟨le_rfl,hkey⟩,
    (D.exact_six_iff b a).2 ⟨le_rfl,hkey.symm⟩⟩

theorem realise_zero_of_no_nonzero_calibration (D : NativeExperiments M I X R Γ Δ)
    (a : D.protocol.State n) (h : D.NoNonzeroCalibration a.profile) :
    ∃ b : D.protocol.State n, b.profile = a.profile ∧ b.law.rate = a.law.rate ∧
      b.law.register = a.law.register ∧ b.law.spectrum = 0 ∧
      D.protocol.Factorable a b ∧ D.protocol.Factorable b a := by
  obtain ⟨b,hp,ht,hreg,hs,_,hab,hba⟩ := D.realise_core a
  rw [(D.spectral_core_empty_iff a.legal.2.2.2.1.1).2 h] at hs
  have hz : b.law.spectrum = 0 := by
    funext i
    by_contra hn
    have hi := mem_support.mpr (show b.law.spectrum i ≠ 0 from hn)
    simp [hs] at hi
  exact ⟨b,hp,ht,hreg,hz,hab,hba⟩

def attainedSpectralSupports (D : NativeExperiments M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) : Set (Finset (M × I)) :=
  {s | ∃ a : D.protocol.State n, a.profile = p ∧ support a.law.spectrum = s}

theorem core_mem_attainedSpectralSupports (D : NativeExperiments M I X R Γ Δ)
    {p : Capabilities M X R Γ Δ n} {s : Finset (M × I)}
    (hs : s ∈ D.attainedSpectralSupports p) :
    core (D.protocol.spectralRows p) s ∈ D.attainedSpectralSupports p := by
  obtain ⟨a,ha,has⟩ := hs
  obtain ⟨b,hb,_,_,hbs,_,_,_⟩ := D.realise_core a
  exact ⟨b,hb.trans ha,by simpa only [ha, has] using hbs⟩

/-- The same interior operator restricts to supports attained at a fixed
profile. The Lean order is reversed to express it as a closure operator. -/
noncomputable def attainedCoreInterior (D : NativeExperiments M I X R Γ Δ)
    (p : Capabilities M X R Γ Δ n) : ClosureOperator (D.attainedSpectralSupports p)ᵒᵈ where
  toFun s := OrderDual.toDual ⟨core (D.protocol.spectralRows p) s.ofDual.val,
    D.core_mem_attainedSpectralSupports s.ofDual.property⟩
  monotone' := fun _ _ h => core_mono_support _ h
  le_closure' s := core_subset _ s.ofDual.val
  idempotent' s := congrArg OrderDual.toDual (Subtype.ext (core_idempotent _ s.ofDual.val))

theorem core_greatest_attained_irreducible (D : NativeExperiments M I X R Γ Δ)
    {p : Capabilities M X R Γ Δ n} {s : Finset (M × I)}
    (hs : s ∈ D.attainedSpectralSupports p) :
    IsGreatest {u | u ⊆ s ∧ u ∈ D.attainedSpectralSupports p ∧
      IrreducibleSupport (D.protocol.spectralRows p) u} (core (D.protocol.spectralRows p) s) := by
  refine ⟨⟨core_subset _ _, D.core_mem_attainedSpectralSupports hs,
    (irreducibleSupport_iff_core_eq _ _).2 (core_idempotent _ _)⟩, ?_⟩
  intro u hu
  exact IrreducibleSupport.subset_core hu.2.2 hu.1

end NativeExperiments

end MovingProjection
