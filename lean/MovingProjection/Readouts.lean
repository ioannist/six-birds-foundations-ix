import MovingProjection.Experiments
import MovingProjection.Effects

/-! Elementary edits specified by measured preparations, decisions at named
grades, licensed comparisons, and available audit receipts. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I]

omit [Fintype R] in
theorem available_imp_iff {p q : Setoid R} :
    (∀ d : R → Bool, Available p d → Available q d) ↔ q ≤ p := by
  classical
  constructor
  · intro h u v huv
    let d (w : R) := decide (p.r u w)
    have hd : Available p d := by
      intro x y hxy
      have hiff : p.r u x ↔ p.r u y :=
        ⟨fun hx => p.trans hx hxy, fun hy => p.trans hy (p.symm hxy)⟩
      simp only [d, hiff]
    have hm := h d hd u v huv
    have ht : d u = true := decide_eq_true (p.refl u)
    exact of_decide_eq_true (hm.symm.trans ht)
  · intro h d hd u v huv
    exact hd u v (h huv)

@[ext] structure NativeReadouts (M X R Γ Δ : Type*) (n : ℕ) where
  trial : M → X × R → X × R → ℚ
  decision : Fin (n+1) → (R → Bool) → Prop
  licensed : Γ → Prop
  cited : Δ → Prop

namespace NativeReadouts

def occurs (a : NativeReadouts M X R Γ Δ n) (p : Proposal M X R) : Prop :=
  0 < a.trial p.1 (p.2.1,p.2.2.2.1) (p.2.2.1,p.2.2.2.2)

def support (a : NativeReadouts M X R Γ Δ n) : Set (Proposal M X R) := {p | a.occurs p}

def advances (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  b.support ⊆ a.support ∧
    (∀ j d, a.decision j d → b.decision j d) ∧
    (∀ g, a.licensed g → b.licensed g) ∧ (∀ e, a.cited e → b.cited e)

def strictlyAdvances (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  a.advances b ∧ ¬ b.advances a

def cover (A : Set (NativeReadouts M X R Γ Δ n)) (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  a.strictlyAdvances b ∧ ∀ r ∈ A, a.strictlyAdvances r → ¬ r.strictlyAdvances b

def near (ε : ℚ) (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  ∀ m x y, |a.trial m x y - b.trial m x y| < ε

def projected (a : NativeReadouts M X R Γ Δ n) (m : M) (x : X × R) (y : X) : ℚ :=
  ∑ v, a.trial m x (y,v)

/-- The experimental definition uses a local change at fixed capabilities, or
a capability cover. A decision, license or receipt edit retains the prepared
law, and a proposal gate retains the prepared projected marked probabilities. -/
def elementary (A : Set (NativeReadouts M X R Γ Δ n)) (ε : ℚ)
    (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  (a.advances b ∧ b.advances a ∧ a.near ε b) ∨
  (cover A a b ∧
    (a.support = b.support → a.trial = b.trial) ∧
    (a.support ≠ b.support → a.projected = b.projected))

/-- The observable that distinguishes each kind of elementary edit. -/
def detects (a b : NativeReadouts M X R Γ Δ n) : Effect → Prop
  | .rewrite => a.advances b ∧ b.advances a
  | .gate => a.support ≠ b.support
  | .route => a.licensed ≠ b.licensed
  | .earlier => ∃ j, j ≠ Fin.last n ∧ a.decision j ≠ b.decision j
  | .terminal => a.decision (Fin.last n) ≠ b.decision (Fin.last n)
  | .publication => a.cited ≠ b.cited

def typedEdit (A : Set (NativeReadouts M X R Γ Δ n)) (ε : ℚ) (e : Effect)
    (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  elementary A ε a b ∧ a.detects b e

end NativeReadouts

namespace NativeExperiments

variable (D : NativeExperiments M I X R Γ Δ) [Nonempty X] [Nonempty R]

def readouts (a : D.protocol.State n) : NativeReadouts M X R Γ Δ n where
  trial := a.law.marked D.parity
  decision j := Available (a.profile.grades j).ofDual
  licensed g := g ∈ a.profile.licenses
  cited e := e ∈ a.profile.published

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
theorem readouts_support (a : D.protocol.State n) :
    (D.readouts a).support = a.profile.mask.ofDual := by
  ext ⟨m,x,y,u,v⟩
  exact D.physical_support a m x y u v

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
theorem readouts_advances_iff (a b : D.protocol.State n) :
    (D.readouts a).advances (D.readouts b) ↔ a.profile ≤ b.profile := by
  rw [NativeReadouts.advances, D.readouts_support, D.readouts_support, Capabilities.le_coordinates]
  refine and_congr_right fun _ => and_congr_left' ?_
  exact forall_congr' fun _ => available_imp_iff

omit [Fintype Γ] [Fintype Δ] in
theorem readouts_eq_iff (a b : D.protocol.State n) : D.readouts a = D.readouts b ↔ a = b := by
  constructor
  · intro h
    have hab := (D.readouts_advances_iff a b).mp (by
      rw [← h]
      exact (D.readouts_advances_iff a a).mpr le_rfl)
    have hba := (D.readouts_advances_iff b a).mp (by
      rw [← h]
      exact (D.readouts_advances_iff a a).mpr le_rfl)
    exact D.state_of_readouts (le_antisymm hab hba) (congrArg NativeReadouts.trial h)
  · rintro rfl
    rfl

abbrev attained (n : ℕ) : Set (NativeReadouts M X R Γ Δ n) :=
  Set.range (D.readouts (n := n))

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
theorem readouts_cover_iff (a b : D.protocol.State n) :
    NativeReadouts.cover (D.attained n) (D.readouts a) (D.readouts b) ↔
      D.protocol.CapCover a.profile b.profile := by
  have strict (x y : D.protocol.State n) :
      (D.readouts x).strictlyAdvances (D.readouts y) ↔ x.profile < y.profile := by
    rw [NativeReadouts.strictlyAdvances, D.readouts_advances_iff, D.readouts_advances_iff,
      lt_iff_le_not_ge]
  constructor
  · intro h
    refine ⟨(strict a b).mp h.1, ?_⟩
    intro p hp hap hpb
    obtain ⟨law,hLaw⟩ := hp
    let c : D.protocol.State n := ⟨p,law,hLaw⟩
    exact h.2 (D.readouts c) ⟨c,rfl⟩ ((strict a c).mpr hap) ((strict c b).mpr hpb)
  · intro h
    refine ⟨(strict a b).mpr h.1, ?_⟩
    rintro _ ⟨c,rfl⟩ hac hcb
    exact h.2 c.profile ⟨c.law,c.legal⟩ ((strict a c).mp hac) ((strict c b).mp hcb)

omit [Fintype Γ] [Fintype Δ] in
theorem readouts_projected_iff (a b : D.protocol.State n) :
    (D.readouts a).projected = (D.readouts b).projected ↔
      a.law.rate = b.law.rate ∧ a.law.spectrum = b.law.spectrum := by
  have formula (s : D.protocol.State n) (m : M) (x : X) (u : R) (y : X) :
      (D.readouts s).projected m (x,u) y =
        s.law.rate m * D.parity.kernel (fun i => s.law.spectrum (m,i)) x y := by
    let a (m : M) (i : I) := s.law.spectrum (m,i)
    change (∑ v, nativeMarked D.parity a s.law.rate s.law.register m (x,u) (y,v)) = _
    exact native_projection D.parity a s.law.rate s.law.register m x y u
      (s.legal.2.2.2.2.1.2.1 m x y u)
  constructor
  · intro h
    let u : R := Classical.choice inferInstance
    have hp (m : M) (x y : X) :
        a.law.rate m * D.parity.kernel (fun i => a.law.spectrum (m,i)) x y =
          b.law.rate m * D.parity.kernel (fun i => b.law.spectrum (m,i)) x y := by
      rw [← formula a m x u, ← formula b m x u, h]
    have hrate : a.law.rate = b.law.rate := by
      funext m
      let x : X := Classical.choice inferInstance
      have H := Finset.sum_congr (s₁ := (Finset.univ : Finset X)) rfl (fun y _ => hp m x y)
      simpa only [← Finset.mul_sum, D.parity.kernel_row_sum, mul_one] using H
    refine ⟨hrate, ?_⟩
    funext ⟨m,i⟩
    have hker : D.parity.kernel (fun j => a.law.spectrum (m,j)) =
        D.parity.kernel (fun j => b.law.spectrum (m,j)) := by
      funext x y
      apply mul_left_cancel₀ (D.δ_pos.trans_le (a.legal.2.2.1.1 m)).ne'
      have hh := hp m x y
      rw [← hrate] at hh
      exact hh
    exact congrFun ((D.parity.kernel_eq_iff _ _).mp hker) i
  · rintro ⟨hRate,hSpec⟩
    funext m ⟨x,u⟩ y
    rw [formula, formula, hRate, hSpec]

omit [Fintype Γ] [Fintype Δ] in
theorem elementary_iff_step (ε : ℚ) (a b : D.protocol.State n) :
    NativeReadouts.elementary (D.attained n) ε (D.readouts a) (D.readouts b) ↔
      ∃ e, D.protocol.Step ε e a b := by
  have hcover := D.readouts_cover_iff a b
  have hproj := D.readouts_projected_iff a b
  have hmask : (D.readouts a).support = (D.readouts b).support ↔ a.profile.mask = b.profile.mask := by
    rw [D.readouts_support, D.readouts_support]
    rfl
  have htrial : (D.readouts a).trial = (D.readouts b).trial ↔ a.law = b.law :=
    ⟨D.measured_law_injective, fun h => congrArg (fun law => law.marked D.parity) h⟩
  constructor
  · rintro (⟨hab,hba,hn⟩ | ⟨hc,hSame,hGate⟩)
    · have h := le_antisymm ((D.readouts_advances_iff a b).mp hab)
        ((D.readouts_advances_iff b a).mp hba)
      exact ⟨.rewrite, by simpa [Protocol.Step] using And.intro h hn⟩
    · have hb := hcover.mp hc
      obtain ⟨e,he,hk⟩ := D.protocol.capKind_of_cover
        ((Protocol.cover_reached_iff (p := a.reached) (q := b.reached)).mpr hb)
      refine ⟨e, ?_⟩
      simp only [Protocol.Step, if_neg he]
      refine ⟨hb,hk,?_⟩
      cases e
      · contradiction
      · exact hproj.mp (hGate (hmask.not.mpr hk.1))
      all_goals
        exact htrial.mp (hSame (hmask.mpr hk.1))
  · rintro ⟨e,he⟩
    by_cases h : e = .rewrite
    · subst e
      obtain ⟨hp,hn⟩ : a.profile = b.profile ∧ PhysicalNear D.parity ε a.law b.law := by
        simpa only [Protocol.Step, if_pos rfl] using he
      exact Or.inl ⟨(D.readouts_advances_iff a b).mpr hp.le,
        (D.readouts_advances_iff b a).mpr hp.symm.le, hn⟩
    · simp only [Protocol.Step, if_neg h] at he
      obtain ⟨hc,hk,hpf⟩ := he
      refine Or.inr ⟨hcover.mpr hc,?_,?_⟩
      · intro hs
        cases e
        · exact (h rfl).elim
        · exact (hk.1 (hmask.mp hs)).elim
        all_goals exact htrial.mpr hpf
      · intro hs
        cases e
        · exact (h rfl).elim
        · exact hproj.mpr hpf
        all_goals exact (hs (hmask.mpr hk.1)).elim

omit [Fintype Γ] [Fintype Δ] [Nonempty X] [Nonempty R] in
theorem readouts_decision_eq_iff (a b : D.protocol.State n) (j : Fin (n+1)) :
    (D.readouts a).decision j = (D.readouts b).decision j ↔
      a.profile.grades j = b.profile.grades j := by
  constructor
  · intro h
    apply le_antisymm
    · apply available_imp_iff.mp
      exact fun d => (congrFun h d).le
    · apply available_imp_iff.mp
      exact fun d => (congrFun h d).symm.le
  · intro h
    change Available (a.profile.grades j).ofDual = Available (b.profile.grades j).ofDual
    rw [h]

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
set_option maxHeartbeats 1500000 in
theorem detected_iff_label {a b : D.protocol.State n} {e : Effect} {ε : ℚ}
    (h : D.protocol.Step ε e a b) (k : Effect) :
    (D.readouts a).detects (D.readouts b) k ↔ k = e := by
  have hMask : (D.readouts a).support = (D.readouts b).support ↔
      a.profile.mask = b.profile.mask := by
    rw [D.readouts_support, D.readouts_support]
    rfl
  have hLic : (D.readouts a).licensed = (D.readouts b).licensed ↔
      a.profile.licenses = b.profile.licenses :=
    ⟨fun h => Finset.ext fun g => iff_of_eq (congrFun h g),
      congrArg (fun s : Finset Γ => fun g => g ∈ s)⟩
  have hPub : (D.readouts a).cited = (D.readouts b).cited ↔
      a.profile.published = b.profile.published :=
    ⟨fun h => Finset.ext fun g => iff_of_eq (congrFun h g),
      congrArg (fun s : Finset Δ => fun g => g ∈ s)⟩
  have hFix : ((D.readouts a).advances (D.readouts b) ∧
      (D.readouts b).advances (D.readouts a)) ↔ a.profile = b.profile := by
    rw [D.readouts_advances_iff, D.readouts_advances_iff]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le,h.symm.le⟩⟩
  have hConst (h : a.profile.grades = b.profile.grades) (j : Fin (n+1)) :
      a.profile.grades j = b.profile.grades j := congrFun h j
  have hEarly (h : SingleGrade a.profile b.profile (Fin.last n)) :
      ¬ ∃ j, j ≠ Fin.last n ∧ a.profile.grades j ≠ b.profile.grades j := by
    rintro ⟨j,hj,hne⟩
    exact hne (h.2 j hj)
  have hLast (j : Fin (n+1)) (hj : j ≠ Fin.last n)
      (h : SingleGrade a.profile b.profile j) :
      a.profile.grades (Fin.last n) = b.profile.grades (Fin.last n) :=
    h.2 _ (Ne.symm hj)
  have hEarlyWitness (h : ∃ j, j ≠ Fin.last n ∧ SingleGrade a.profile b.profile j) :
      ∃ j, j ≠ Fin.last n ∧ a.profile.grades j ≠ b.profile.grades j := by
    obtain ⟨j,hj,hs⟩ := h
    exact ⟨j,hj,hs.1⟩
  have hNotFix : D.protocol.CapCover a.profile b.profile → a.profile ≠ b.profile :=
    fun hc => hc.1.ne
  cases e <;> cases k <;>
    simp [Protocol.Step, CapKind, NativeReadouts.detects, hFix, hMask, hLic, hPub,
      D.readouts_decision_eq_iff, SingleGrade] at h ⊢ <;>
    first | exact hEarlyWitness h.2.1.2.2.2 | aesop

omit [Fintype Γ] [Fintype Δ] in
theorem typed_edit_iff_step (ε : ℚ) (e : Effect) (a b : D.protocol.State n) :
    NativeReadouts.typedEdit (D.attained n) ε e (D.readouts a) (D.readouts b) ↔
      D.protocol.Step ε e a b := by
  constructor
  · rintro ⟨he,hkind⟩
    obtain ⟨k,hk⟩ := (D.elementary_iff_step ε a b).mp he
    rwa [(D.detected_iff_label hk e).mp hkind]
  · intro h
    exact ⟨(D.elementary_iff_step ε a b).mpr ⟨e,h⟩,
      (D.detected_iff_label h e).mpr rfl⟩

omit [Fintype Γ] [Fintype Δ] in
theorem elementary_iff_unique_effect (ε : ℚ) (a b : D.protocol.State n) :
    NativeReadouts.elementary (D.attained n) ε (D.readouts a) (D.readouts b) ↔
      ∃! e, D.protocol.Step ε e a b := by
  rw [D.elementary_iff_step ε a b]
  constructor
  · rintro ⟨e,he⟩
    refine ⟨e,he,fun k hk => ?_⟩
    exact (D.detected_iff_label he k).mp ((D.detected_iff_label hk k).mpr rfl)
  · exact ExistsUnique.exists

end NativeExperiments
end MovingProjection
