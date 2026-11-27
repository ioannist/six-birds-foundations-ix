import MovingProjection.ReadoutChains

/-! Finite record tables for the experimental measurements. Exact read-back
preserves and reflects the edit language, including the omission languages. -/

namespace MovingProjection

open scoped BigOperators

structure QueryTables (M X R Γ Δ : Type*) (n : ℕ) where
  measured : Finset ((M × (X × R) × (X × R)) × ℚ)
  decisions : Finset (Fin (n+1) × (R → Bool))
  licenses : Finset Γ
  receipts : Finset Δ

namespace QueryTables

variable {M X R Γ Δ : Type*} {n : ℕ}

noncomputable def ofReadouts [Fintype M] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
    (a : NativeReadouts M X R Γ Δ n) : QueryTables M X R Γ Δ n := by
  classical
  exact {
    measured := Finset.univ.image fun k => (k,a.trial k.1 k.2.1 k.2.2)
    decisions := Finset.univ.filter fun p => a.decision p.1 p.2
    licenses := Finset.univ.filter a.licensed
    receipts := Finset.univ.filter a.cited }

noncomputable def readBack (cert : QueryTables M X R Γ Δ n) : NativeReadouts M X R Γ Δ n := by
  classical
  exact {
    trial := fun m x y => ∑ e ∈ cert.measured.filter (fun e => e.1 = (m,x,y)), e.2
    decision := fun j p => (j,p) ∈ cert.decisions
    licensed := fun g => g ∈ cert.licenses
    cited := fun c => c ∈ cert.receipts }

theorem measured_row_iff [Fintype M] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
    (a : NativeReadouts M X R Γ Δ n) (m : M) (x y : X × R) (q : ℚ) :
    ((m,x,y),q) ∈ (ofReadouts a).measured ↔ q = a.trial m x y := by
  classical
  change ((m,x,y),q) ∈ Finset.univ.image
    (fun k : M × (X × R) × (X × R) => (k,a.trial k.1 k.2.1 k.2.2)) ↔ _
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp h
    have h₁ := congrArg Prod.fst hk
    have h₂ := congrArg Prod.snd hk
    change k = (m,x,y) at h₁
    subst k
    exact h₂.symm
  · intro h
    subst q
    exact Finset.mem_image.mpr ⟨(m,x,y),Finset.mem_univ _,rfl⟩

@[simp] theorem readBack_ofReadouts [Fintype M] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
    (a : NativeReadouts M X R Γ Δ n) : (ofReadouts a).readBack = a := by
  classical
  have htrial : (ofReadouts a).readBack.trial = a.trial := by
    funext m x y
    have single : (ofReadouts a).measured.filter (fun e => e.1 = (m,x,y)) =
        {((m,x,y),a.trial m x y)} := by
      ext ⟨⟨m',x',y'⟩,q⟩
      simp only [Finset.mem_filter, Finset.mem_singleton, measured_row_iff]
      constructor
      · rintro ⟨hq,hkey⟩
        subst q
        exact Prod.ext hkey (congrArg (fun k : M × (X × R) × (X × R) =>
          a.trial k.1 k.2.1 k.2.2) hkey)
      · intro h
        have hkey := congrArg Prod.fst h
        have hvalue := congrArg Prod.snd h
        exact ⟨hvalue.trans (congrArg (fun k : M × (X × R) × (X × R) =>
          a.trial k.1 k.2.1 k.2.2) hkey).symm,hkey⟩
    change (∑ e ∈ (ofReadouts a).measured.filter (fun e => e.1 = (m,x,y)), e.2) = _
    rw [single,Finset.sum_singleton]
  have hdecisions : (ofReadouts a).readBack.decision = a.decision := by
    funext j p
    apply propext
    simp [readBack,ofReadouts]
  have hlicenses : (ofReadouts a).readBack.licensed = a.licensed := by
    funext g
    apply propext
    simp [readBack,ofReadouts]
  have hreceipts : (ofReadouts a).readBack.cited = a.cited := by
    funext c
    apply propext
    simp [readBack,ofReadouts]
  exact NativeReadouts.ext htrial hdecisions hlicenses hreceipts

end QueryTables

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [Nonempty X] [Nonempty R]
  (D : NativeExperiments M I X R Γ Δ)

noncomputable def tables (a : D.protocol.State n) : QueryTables M X R Γ Δ n :=
  QueryTables.ofReadouts (D.readouts a)

omit [Nonempty X] [Nonempty R] in
@[simp] theorem tables_readBack (a : D.protocol.State n) :
    (D.tables a).readBack = D.readouts a := QueryTables.readBack_ofReadouts _

theorem tables_eq_iff (a b : D.protocol.State n) : D.tables a = D.tables b ↔ a = b := by
  constructor
  · intro h
    apply (D.readouts_eq_iff a b).mp
    simpa using congrArg QueryTables.readBack h
  · rintro rfl
    rfl

abbrev TableSpace (n : ℕ) := Set.range (D.tables (n := n))

noncomputable def record : D.protocol.State n ≃ D.TableSpace n :=
  Equiv.ofInjective D.tables (fun a b h => (D.tables_eq_iff a b).mp h)

abbrev TableChain (ε : ℚ) :=
  Relation.ReflTransGen (fun a b : D.TableSpace n =>
    NativeReadouts.elementary (D.attained n) ε a.val.readBack b.val.readBack)

theorem table_chain_iff (ε : ℚ) (a b : D.protocol.State n) :
    D.TableChain ε (D.record a) (D.record b) ↔ D.protocol.Chain ε a b := by
  apply chain_equiv D.record _ a b
  intro a b
  change NativeReadouts.elementary (D.attained n) ε
      (D.tables a).readBack (D.tables b).readBack ↔ _
  simpa using D.elementary_iff_step ε a b

theorem table_factorization_iff (a b : D.protocol.State n) :
    (∀ ε : ℚ, 0 < ε → D.TableChain ε (D.record a) (D.record b)) ↔ D.protocol.Factorable a b :=
  ⟨fun h ε hε => (D.table_chain_iff ε a b).mp (h ε hε),
    fun h ε hε => (D.table_chain_iff ε a b).mpr (h ε hε)⟩

theorem table_exact_six [Nonempty M] (a b : D.protocol.State n) (x : X × R) :
    (∀ ε : ℚ, 0 < ε → D.TableChain ε (D.record a) (D.record b)) ↔
      (D.tables a).readBack.advances (D.tables b).readBack ∧
        D.readoutSignature (D.tables a).readBack (D.tables a).readBack x =
          D.readoutSignature (D.tables a).readBack (D.tables b).readBack x := by
  rw [D.table_factorization_iff, D.tables_readBack, D.tables_readBack,
    D.readouts_advances_iff, D.readoutSignature_correct, D.readoutSignature_correct,
    D.exact_six_iff]

/-- Equivalent presentations carry the same named tests after translating
the query names into the common native vocabulary. Their elementary effect
types therefore agree at each tolerance. -/
theorem same_tests_same_effect {A B : Type*}
    (first : A → D.protocol.State n) (second : B → D.protocol.State n) (translate : A ≃ B)
    (agree : ∀ u, D.tables (first u) = D.tables (second (translate u)))
    (ε : ℚ) (e : Effect) (u v : A) :
    D.protocol.Step ε e (first u) (first v) ↔
      D.protocol.Step ε e (second (translate u)) (second (translate v)) := by
  rw [(D.tables_eq_iff _ _).mp (agree u), (D.tables_eq_iff _ _).mp (agree v)]

end NativeExperiments
end MovingProjection
