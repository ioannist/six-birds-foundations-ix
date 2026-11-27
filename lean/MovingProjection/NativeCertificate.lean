import MovingProjection.CertificateComplete

/-! A native certificate checker on explicitly presented profiles. The
support is recovered from the registered law, and a partition is presented
by a block label for each register value at each grade. -/

namespace MovingProjection.CoreCertificate

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq Γ] [DecidableEq Δ]
  [Nonempty M] [Nonempty X] [Nonempty R]

structure ProfileTable (R Γ Δ : Type*) [Fintype R] (n : ℕ) where
  label : Fin (n+1) → R → Fin (Fintype.card R)
  licenses : Finset Γ
  published : Finset Δ

def ProfileTable.profile (p : ProfileTable R Γ Δ n) (law : PhysicalLaw M I X R) :
    Capabilities M X R Γ Δ n where
  mask := OrderDual.toDual (registerMask law.register)
  grades i := OrderDual.toDual (Setoid.ker (p.label i))
  licenses := p.licenses
  published := p.published

def maskTest (law : PhysicalLaw M I X R) (p : Proposal M X R) : Bool :=
  decide (law.register p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 > 0)

def ProfileTable.leCheck (p q : ProfileTable R Γ Δ n) (a b : PhysicalLaw M I X R) : Bool :=
  decide (∀ t : Proposal M X R, maskTest b t = true → maskTest a t = true) &&
  decide (∀ i u v, q.label i u = q.label i v → p.label i u = p.label i v) &&
  decide (p.licenses ⊆ q.licenses) && decide (p.published ⊆ q.published)

omit [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq I]
  [Nonempty M] [Nonempty X] [Nonempty R] in
theorem ProfileTable.leCheck_correct (p q : ProfileTable R Γ Δ n) (a b : PhysicalLaw M I X R) :
    p.leCheck q a b = true ↔ p.profile a ≤ q.profile b := by
  rw [Capabilities.le_coordinates]
  simp only [leCheck, Bool.and_eq_true, decide_eq_true_eq, profile, OrderDual.ofDual_toDual]
  have hm : (∀ t : Proposal M X R, maskTest b t = true → maskTest a t = true) ↔
      registerMask b.register ⊆ registerMask a.register := by
    simp only [maskTest, decide_eq_true_eq]
    rfl
  have hg : (∀ i u v, q.label i u = q.label i v → p.label i u = p.label i v) ↔
      (∀ i, Setoid.ker (q.label i) ≤ Setoid.ker (p.label i)) := by
    simp only [Setoid.le_def]
    exact ⟨fun h i {_ _} => h i _ _, fun h i _ _ => h i⟩
  rw [hm, hg]
  tauto

structure Presented (D : NativeExperiments M I X R Γ Δ) (n : ℕ) where
  table : ProfileTable R Γ Δ n
  law : PhysicalLaw M I X R
  legal : D.protocol.legal (table.profile law) law

def Presented.state {D : NativeExperiments M I X R Γ Δ} (a : Presented D n) :
    D.protocol.State n := ⟨a.table.profile a.law, a.law, a.legal⟩

noncomputable def Presented.rows {D : NativeExperiments M I X R Γ Δ} (a : Presented D n) :=
  (D.protocol.fiber a.state.profile).spectralChecks.map MonomialTest.row

/-- The explicit rows are supplied by the instrument's compilation.
A failed directed order test needs no support-reduction witnesses. -/
def nativeCheck (rows : List (ExponentRow (M × I))) (p q : ProfileTable R Γ Δ n)
    (a b : PhysicalLaw M I X R) (left right : Witness rows) : Option Bool :=
  if p.leCheck q a b then checkPair rows a.spectrum b.spectrum left right else some false

theorem nativeCheck_sound (D : NativeExperiments M I X R Γ Δ) (a b : Presented D n)
    {left right : Witness a.rows} {answer : Bool}
    (h : nativeCheck a.rows a.table b.table a.law b.law left right = some answer) :
    answer = true ↔ D.protocol.Factorable a.state b.state := by
  by_cases hp : a.table.leCheck b.table a.law b.law = true
  · have hle : a.state.profile ≤ b.state.profile :=
      (ProfileTable.leCheck_correct ..).mp hp
    simp only [nativeCheck, hp, if_true] at h
    exact ((native_certificate D a.state b.state h).trans (and_iff_right hle)).symm
  · have hn : ¬a.state.profile ≤ b.state.profile :=
      fun hh => hp ((ProfileTable.leCheck_correct ..).mpr hh)
    simp only [nativeCheck, if_neg hp, Option.some.injEq] at h
    subst answer
    simp only [Bool.false_eq_true, false_iff]
    intro hf
    exact hn (Protocol.Chain.profile_le (hf 1 zero_lt_one))

omit [Fintype Γ] [Fintype Δ] [Nonempty M] [Nonempty X] [Nonempty R] in
theorem nativeCheck_complete (D : NativeExperiments M I X R Γ Δ) (a b : Presented D n) :
    ∃ left right, ∃ answer, nativeCheck a.rows a.table b.table a.law b.law left right = some answer := by
  obtain ⟨left, right, answer, ha⟩ := checkPair_complete a.rows a.law.spectrum b.law.spectrum
  by_cases hp : a.table.leCheck b.table a.law b.law = true
  · exact ⟨left, right, answer, by simpa only [nativeCheck, hp, if_true] using ha⟩
  · exact ⟨left, right, false, by simp only [nativeCheck, if_neg hp]⟩

end MovingProjection.CoreCertificate
