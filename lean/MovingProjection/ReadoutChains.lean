import MovingProjection.Readouts

/-! Transport between the prepared-query records and the original audited
Markov laws, including all tests used to rule out chains. -/

namespace MovingProjection

theorem chain_equiv {A B : Type*} (f : A ≃ B)
    {r : A → A → Prop} {s : B → B → Prop} (h : ∀ u v, s (f u) (f v) ↔ r u v) (a b : A) :
    Relation.ReflTransGen s (f a) (f b) ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro hs
    have hr := hs.lift f.symm (fun u v huv => (h (f.symm u) (f.symm v)).mp (by simpa using huv))
    simpa using hr
  · exact fun hr => hr.lift f (fun u v huv => (h u v).mpr huv)

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [Nonempty X] [Nonempty R]
  (D : NativeExperiments M I X R Γ Δ)

noncomputable def observe : D.protocol.State n ≃ D.attained n :=
  Equiv.ofInjective D.readouts (fun _ _ h => (D.readouts_eq_iff _ _).mp h)

abbrev ReadoutChain (ε : ℚ) :=
  Relation.ReflTransGen (fun a b : D.attained n =>
    NativeReadouts.elementary (D.attained n) ε a.val b.val)

omit [Fintype Γ] [Fintype Δ] in
theorem readoutChain_iff (ε : ℚ) (a b : D.protocol.State n) :
    D.ReadoutChain ε (D.observe a) (D.observe b) ↔ D.protocol.Chain ε a b :=
  chain_equiv D.observe (D.elementary_iff_step ε) a b

omit [Fintype Γ] [Fintype Δ] in
theorem readouts_factorization_iff (a b : D.protocol.State n) :
    (∀ ε : ℚ, 0 < ε → D.ReadoutChain ε (D.observe a) (D.observe b)) ↔
      D.protocol.Factorable a b :=
  ⟨fun h ε hε => (D.readoutChain_iff ε a b).mp (h ε hε),
    fun h ε hε => (D.readoutChain_iff ε a b).mpr (h ε hε)⟩

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
theorem readouts_spectrum (a : D.protocol.State n) (x : X × R) (m : M) (i : I) :
    observedSignal D.parity (D.readouts a).trial m x i /
      observedRate (D.readouts a).trial m x = a.law.spectrum (m,i) := by
  let f (m : M) (i : I) := a.law.spectrum (m,i)
  let P := nativeMarked D.parity f a.law.rate a.law.register
  have h := a.legal.2.2.2.2.1.2.1
  have hp := D.δ_pos.trans_le (a.legal.2.2.1.1 m)
  change observedSignal D.parity P m x i / observedRate P m x = f m i
  rw [observedSignal_native _ _ _ _ h, observedRate_native _ _ _ _ h]
  exact mul_div_cancel_left₀ _ hp.ne'

noncomputable def readoutSignature (a b : NativeReadouts M X R Γ Δ n) (x : X × R) :
    M × I → SignType := by
  classical
  let tests := D.protocol.checks.spectralTests
    (Finset.univ.filter a.licensed) (Finset.univ.filter a.cited)
  exact signedCore (tests.map MonomialTest.row) (signCode (embed fun mi =>
    observedSignal D.parity b.trial mi.1 x mi.2 / observedRate b.trial mi.1 x))

omit [Nonempty R] in
theorem readoutSignature_correct (a b : D.protocol.State n) (x : X × R) :
    D.readoutSignature (D.readouts a) (D.readouts b) x = D.protocol.signature a.profile b.law := by
  classical
  have hLicense : Finset.univ.filter (D.readouts a).licensed = a.profile.licenses := by
    ext g
    simp [readouts]
  have hCitation : Finset.univ.filter (D.readouts a).cited = a.profile.published := by
    ext e
    simp [readouts]
  have hSpectrum :
      (fun mi : M × I => observedSignal D.parity (D.readouts b).trial mi.1 x mi.2 /
        observedRate (D.readouts b).trial mi.1 x) = b.law.spectrum := by
    funext ⟨m,i⟩
    exact D.readouts_spectrum b x m i
  simp only [readoutSignature, Protocol.signature, Protocol.fiber, hLicense, hCitation, hSpectrum]

theorem exact_six_on_readouts [Nonempty M] (a b : D.protocol.State n) (x : X × R) :
    (∀ ε : ℚ, 0 < ε → D.ReadoutChain ε (D.observe a) (D.observe b)) ↔
      (D.readouts a).advances (D.readouts b) ∧
      D.readoutSignature (D.readouts a) (D.readouts a) x =
        D.readoutSignature (D.readouts a) (D.readouts b) x := by
  rw [D.readouts_factorization_iff, D.readouts_advances_iff,
    D.readoutSignature_correct, D.readoutSignature_correct, D.exact_six_iff]

end NativeExperiments
end MovingProjection
