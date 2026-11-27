import MovingProjection.NativeCoreOrder
import MovingProjection.CommitLateExample

/-! Sharp examples for the anchor statement and the direction of closure. -/

namespace MovingProjection.CoreOrderExamples

open scoped BigOperators

/-- The test is `(x(false) * x(true))^2 = x(false) * x(true)`. Its full
support forces the product to be one, and both monomials vanish at zero. -/
def productTest : MonomialTest Bool := ⟨⟨fun _ => 2, fun _ => 1⟩, 1⟩

def productBudgets : List (MarkBudget Bool) := [⟨Finset.univ, 2⟩]

def productPoint (negative : Bool) : Bool → ℚ := fun _ => if negative then -1 else 1

theorem product_legal (negative : Bool) : Legal [productTest] productBudgets (productPoint negative) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain rfl := List.mem_singleton.mp ht
    cases negative <;> norm_num [MonomialTest.holds, productTest, productPoint, monomial,
      Fintype.prod_bool]
  · intro b hb
    obtain rfl := List.mem_singleton.mp hb
    cases negative <;> norm_num [productBudgets, productPoint, Fintype.sum_bool]

theorem product_zero_legal : Legal [productTest] productBudgets 0 := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain rfl := List.mem_singleton.mp ht
    norm_num [MonomialTest.holds, productTest, monomial, Fintype.prod_bool]
  · intro b hb
    obtain rfl := List.mem_singleton.mp hb
    norm_num [productBudgets]

theorem product_core : core [productTest.row] Finset.univ = Finset.univ := by
  apply core_eq_self_of_damping_zero
  intro w hw i _
  have ha : productTest.row.active Finset.univ := by simp [ExponentRow.active]
  have h := hw.2 _ (by simp) ha
  simp [productTest] at h
  cases i <;> omega

private theorem product_signed_core (negative : Bool) :
    signedCore [productTest.row] (signCode (embed (productPoint negative))) =
      fun _ => if negative then (-1 : SignType) else 1 := by
  have hs : codeSupport (signCode (embed (productPoint negative))) = Finset.univ := by
    rw [codeSupport_signCode, show realSupport (embed (productPoint negative)) =
      support (productPoint negative) from realSupport_cast _]
    ext j
    cases negative <;> simp [productPoint]
  funext j
  simp only [signedCore, hs, product_core, Finset.mem_univ, if_true]
  cases negative
  · apply sign_pos
    norm_num [embed, productPoint]
  · apply sign_neg
    norm_num [embed, productPoint]

theorem product_not_fineConnected :
    ¬ FineConnected [productTest] productBudgets (productPoint false) (productPoint true) := by
  intro h
  have hkey := fineConnected_signedCore
    (bounded_of_budget_cover (tests := [productTest]) (budgets := productBudgets)
      (fun j => ⟨⟨Finset.univ,2⟩, by simp [productBudgets], Finset.mem_univ j⟩)) h
  change signedCore [productTest.row] (signCode (embed (productPoint false))) =
    signedCore [productTest.row] (signCode (embed (productPoint true))) at hkey
  rw [product_signed_core, product_signed_core] at hkey
  exact (by decide : (1 : SignType) ≠ -1) (congrFun hkey false)

namespace Native

open CommitLateExample

abbrev Index := Bool × Unit

private theorem audit_mem (held : Bool) :
    (calibrationTest true () (1/4)).row ∈ D.spectralRows (profile held) := by
  apply List.mem_map_of_mem
  change calibrationTest true () (1/4) ∈ D.checks.spectralTests (profile held).licenses {()}
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(), by simp,
    by simp [NativeExperiments.protocol, instrument]⟩)

private theorem core_row_before (r : ExponentRow Index)
    (hr : r ∈ D.spectralRows (profile false)) :
    (∃ i, r = (reversalTest id i).row) ∨ r = (calibrationTest true () (1/4)).row := by
  obtain ⟨test,htest,heq⟩ := List.mem_map.mp hr
  subst r
  change test ∈ D.checks.spectralTests ∅ {()} at htest
  have h : (∃ i, test = reversalTest id i) ∨ test = calibrationTest true () (1/4) := by
    simpa [NativeExperiments.protocol, instrument, ProbeCatalog.spectralTests,
      eq_comm] using htest
  rcases h with ⟨i,rfl⟩ | rfl
  · exact Or.inl ⟨i,rfl⟩
  · exact Or.inr rfl

theorem core_before {s : Finset Index} (ha : (true,()) ∈ s) :
    core (D.spectralRows (profile false)) s = {(true,())} := by
  let w (j : Index) : ℕ := if j.1 = false ∧ j ∈ s then 1 else 0
  have hcon : Contracts (D.spectralRows (profile false)) s {(true,())} := by
    refine ⟨w, ⟨fun j hj => by simp [w,hj], ?_⟩, ?_⟩
    · intro r hr _
      rcases core_row_before r hr with ⟨i,rfl⟩ | rfl
      · rfl
      · simp [calibrationTest, pointExponent, w]
    · ext ⟨m,i⟩
      cases i
      cases m <;> simp [w, ha]
  exact Finset.Subset.antisymm ((isCore_core _ _).2 _ (.single hcon))
    (Finset.singleton_subset_iff.mpr (calibration_mem_core (audit_mem false) ha))

private theorem compare_mem :
    (routeCharacterTest [false,false] [true,true] ()).row ∈ D.spectralRows (profile true) := by
  apply List.mem_map_of_mem
  change routeCharacterTest [false,false] [true,true] () ∈ D.checks.spectralTests {()} {()}
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨(),by simp, List.mem_map_of_mem (by simp)⟩

theorem core_after :
    core (D.spectralRows (profile true)) (Finset.univ : Finset Index) = Finset.univ := by
  apply core_eq_self_of_damping_zero
  intro w hw i _
  have ha (r : ExponentRow Index) : r.active Finset.univ := by simp [ExponentRow.active]
  have hb := hw.2 _ (audit_mem true) (ha _)
  have hr := hw.2 _ compare_mem (ha _)
  have hb' : w (true,()) = 0 := by simpa [calibrationTest, pointExponent] using hb
  have hr' : 2 * w (false,()) = 2 * w (true,()) := by
    simpa [routeCharacterTest, characterExponent, Fintype.sum_prod_type] using hr
  have hx : w (false,()) = 0 := by omega
  rcases i with ⟨i,⟨⟩⟩
  cases i
  · exact hx
  · exact hb'

private theorem source_support : support source.law.spectrum = Finset.univ := by
  ext ⟨m,i⟩
  cases i
  change (m,()) ∈ support (law (1/4)).spectrum ↔ (m,()) ∈ Finset.univ
  cases m <;> norm_num [law]

theorem strict_core_growth :
    core (D.spectralRows source.profile) (support source.law.spectrum) = {(true,())} ∧
    core (D.spectralRows early.profile) (support source.law.spectrum) = Finset.univ := by
  rw [source_support]
  exact ⟨core_before (Finset.mem_univ _),core_after⟩

theorem core_not_extensive_on_attained_supports :
    ¬ support source.law.spectrum ⊆ core (D.spectralRows source.profile) (support source.law.spectrum) := by
  rw [strict_core_growth.1, source_support]
  intro h
  have hmem := h (a := (false,())) (Finset.mem_univ _)
  simp at hmem

private theorem calibration_signature (a : State) (ha : () ∈ a.profile.published) :
    D.signature (profile false) a.law = fun j => if j = (true,()) then 1 else 0 := by
  have hcal : a.law.spectrum (true,()) = 1/4 :=
    instrument.calibration_value a ha rfl
  have hs : codeSupport (signCode (embed a.law.spectrum)) = support a.law.spectrum :=
    (codeSupport_signCode _).trans (realSupport_cast _)
  have hcore := core_before (mem_support.mpr (hcal ▸ (by norm_num : (1/4 : ℚ) ≠ 0)))
  funext j
  unfold Protocol.signature signedCore
  rw [hs, hcore]
  by_cases hj : j = (true,())
  · subst j
    simp only [Finset.mem_singleton_self, if_true]
    apply sign_pos
    norm_num [embed,hcal]
  · simp [hj]

theorem calibration_alone_no_obstruction (a b : State) (hp : a.profile = profile false) :
    D.Factorable a b ↔ a.profile ≤ b.profile := by
  rw [instrument.exact_six_iff]
  constructor
  · exact And.left
  · intro hab
    have ha : () ∈ a.profile.published := by simp [hp,profile]
    have hb := (Capabilities.le_coordinates.mp hab).2.2.2 ha
    exact ⟨hab, hp ▸ (calibration_signature a ha).trans (calibration_signature b hb).symm⟩

/-- Both laws already pass the added route test. At the old profile the
pair is connected, and at the new profile it is separated. -/
theorem strict_reachability_split :
    D.Factorable source beforeCommitment ∧
      ¬ D.Factorable early target ∧
      source.law = early.law ∧ beforeCommitment.law = target.law :=
  ⟨late_numerical, early_not_factorable,rfl,rfl⟩

/-- A zero calibration is harmless on its lawful laws but can give a
nonempty core on a formal support inconsistent with the calibration. -/
def zeroInstrument : NativeExperiments Bool Unit Bool Unit Unit Unit :=
  {instrument with audit := fun _ => .calibration true () 0}

private theorem zero_calibration_mem :
    calibrationTest true () 0 ∈ (zeroInstrument.protocol.fiber (profile false)).spectralChecks := by
  change calibrationTest true () 0 ∈ zeroInstrument.protocol.checks.spectralTests ∅ {()}
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(), by simp,
    by simp [zeroInstrument, NativeExperiments.protocol]⟩)

noncomputable def zeroState : zeroInstrument.protocol.State 0 := by
  let l : PhysicalLaw Bool Unit Bool Unit := {source.law with spectrum := 0}
  refine ⟨profile false,l,source.legal.1,trivial,source.legal.2.2.1,
    ⟨?_,?_⟩,source.legal.2.2.2.2⟩
  · intro test htest
    change test ∈ zeroInstrument.protocol.checks.spectralTests ∅ {()} at htest
    have h : (∃ j, test = reversalTest id j) ∨ test = calibrationTest true () 0 := by
      simpa [zeroInstrument, instrument, NativeExperiments.protocol, ProbeCatalog.spectralTests,
        eq_comm] using htest
    rcases h with ⟨j,rfl⟩ | rfl
    · simp [MonomialTest.holds, reversalTest]
    · simp [MonomialTest.holds, calibrationTest, pointMonomial, l]
  · intro b hb
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
    norm_num [l,zeroInstrument,instrument,NativeExperiments.protocol]

theorem zero_calibration_formal_support :
    zeroInstrument.NoNonzeroCalibration zeroState.profile ∧
    core (zeroInstrument.protocol.spectralRows zeroState.profile) {(true,())} = {(true,())} ∧
    ¬ {(true,())} ∈ zeroInstrument.attainedSpectralSupports zeroState.profile := by
  refine ⟨?_, ?_, ?_⟩
  · intro e _ m i c h
    change AuditQuery.calibration (true : Bool) () 0 = .calibration m i c at h
    cases h
    rfl
  · have hm := calibration_mem_core (List.mem_map_of_mem zero_calibration_mem)
      (Finset.mem_singleton_self (true,()))
    exact Finset.Subset.antisymm (core_subset _ _) (Finset.singleton_subset_iff.mpr hm)
  · rintro ⟨a,hp,hs⟩
    have h := zeroInstrument.calibration_value a (e := ()) (by rw [hp]; simp [zeroState, profile])
      (rfl : zeroInstrument.audit () = .calibration true () 0)
    have hi : (true,()) ∈ support a.law.spectrum := by rw [hs]; simp
    exact (mem_support.mp hi) h

end Native

end MovingProjection.CoreOrderExamples
