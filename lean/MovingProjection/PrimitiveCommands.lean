import MovingProjection.Readouts

/-! Native command parameters and the uniform timed decision write. -/

namespace MovingProjection

/-- A position in the experimental edit contract. The clock index is a
parameter of the decision write, including at the terminal grade. -/
inductive EditPosition (n : ℕ)
  | localLaw
  | support
  | decision (grade : Fin (n+1))
  | license
  | receipt
  deriving DecidableEq

def EditPosition.effect {n : ℕ} : EditPosition n → Effect
  | .localLaw => .rewrite
  | .support => .gate
  | .decision j => if j = Fin.last n then .terminal else .earlier
  | .license => .route
  | .receipt => .publication

@[simp] theorem EditPosition.effect_eq_rewrite {n : ℕ} (p : EditPosition n) :
    p.effect = .rewrite ↔ p = .localLaw := by
  cases p <;> simp [effect]
  split <;> simp

@[simp] theorem EditPosition.effect_eq_gate {n : ℕ} (p : EditPosition n) :
    p.effect = .gate ↔ p = .support := by
  cases p <;> simp [effect]
  split <;> simp

@[simp] theorem EditPosition.effect_eq_route {n : ℕ} (p : EditPosition n) :
    p.effect = .route ↔ p = .license := by
  cases p <;> simp [effect]
  split <;> simp

@[simp] theorem EditPosition.effect_eq_publication {n : ℕ} (p : EditPosition n) :
    p.effect = .publication ↔ p = .receipt := by
  cases p <;> simp [effect]
  split <;> simp

namespace NativeReadouts

variable {M X R Γ Δ : Type*} {n : ℕ}

def positionChanged (a b : NativeReadouts M X R Γ Δ n) : EditPosition n → Prop
  | .localLaw => a.advances b ∧ b.advances a
  | .support => a.support ≠ b.support
  | .decision j => a.decision j ≠ b.decision j
  | .license => a.licensed ≠ b.licensed
  | .receipt => a.cited ≠ b.cited

def editAt [Fintype R] (attained : Set (NativeReadouts M X R Γ Δ n)) (ε : ℚ)
    (p : EditPosition n) (a b : NativeReadouts M X R Γ Δ n) : Prop :=
  elementary attained ε a b ∧ a.positionChanged b p

def writeDecision (a : NativeReadouts M X R Γ Δ n) (j : Fin (n+1))
    (available : (R → Bool) → Prop) : NativeReadouts M X R Γ Δ n :=
  { a with decision := Function.update a.decision j available }

end NativeReadouts

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I] [Nonempty X] [Nonempty R]
  (D : NativeExperiments M I X R Γ Δ)

abbrev EditAt (ε : ℚ) (p : EditPosition n) (a b : D.protocol.State n) :=
  NativeReadouts.editAt (D.attained n) ε p (D.readouts a) (D.readouts b)

theorem editAt_step {ε : ℚ} {p : EditPosition n} {a b : D.protocol.State n}
    (h : D.EditAt ε p a b) : D.protocol.Step ε p.effect a b := by
  apply (D.typed_edit_iff_step ε p.effect a b).mp
  refine ⟨h.1,?_⟩
  cases p with
  | decision j =>
    by_cases hj : j = Fin.last n
    · subst j
      simp only [EditPosition.effect]
      exact h.2
    · simp only [EditPosition.effect, if_neg hj, NativeReadouts.detects]
      exact ⟨j,hj,h.2⟩
  | localLaw => exact h.2
  | support => exact h.2
  | license => exact h.2
  | receipt => exact h.2

theorem step_iff_editAt {ε : ℚ} {e : Effect} {a b : D.protocol.State n} :
    D.protocol.Step ε e a b ↔ ∃ p : EditPosition n, p.effect = e ∧ D.EditAt ε p a b := by
  constructor
  · intro h
    obtain ⟨he,hd⟩ := (D.typed_edit_iff_step ε e a b).mpr h
    cases e with
    | rewrite => exact ⟨.localLaw,rfl,he,hd⟩
    | gate => exact ⟨.support,rfl,he,hd⟩
    | route => exact ⟨.license,rfl,he,hd⟩
    | publication => exact ⟨.receipt,rfl,he,hd⟩
    | earlier =>
      obtain ⟨j,hj,hc⟩ := hd
      exact ⟨.decision j,if_neg hj,he,hc⟩
    | terminal => exact ⟨.decision (Fin.last n),if_pos rfl,he,hd⟩
  · rintro ⟨p,hp,he⟩
    exact hp ▸ D.editAt_step he

omit [Nonempty X] [Nonempty R] in
private theorem grade_change_of_step {ε : ℚ} {e : Effect} {a b : D.protocol.State n}
    (h : D.protocol.Step ε e a b) :
    a.profile.grades = b.profile.grades ∨
      ((e = .earlier ∨ e = .terminal) ∧ ∃ j, SingleGrade a.profile b.profile j) := by
  cases e with
  | rewrite =>
    have h' : a.profile = b.profile ∧ PhysicalNear D.parity ε a.law b.law := h
    exact Or.inl (congrArg Capabilities.grades h'.1)
  | gate =>
    have h' : CapKind .gate a.profile b.profile := h.2.1
    exact Or.inl h'.2.1
  | route =>
    have h' : CapKind .route a.profile b.profile := h.2.1
    exact Or.inl h'.2.1
  | publication =>
    have h' : CapKind .publication a.profile b.profile := h.2.1
    exact Or.inl h'.2.1
  | earlier =>
    have h' : CapKind .earlier a.profile b.profile := h.2.1
    obtain ⟨j,_,hg⟩ := h'.2.2.2
    exact Or.inr ⟨Or.inl rfl,j,hg⟩
  | terminal =>
    have h' : CapKind .terminal a.profile b.profile := h.2.1
    exact Or.inr ⟨Or.inr rfl,Fin.last n,h'.2.2.2⟩

theorem editAt_decision_singleGrade {ε : ℚ} {j : Fin (n+1)} {a b : D.protocol.State n}
    (h : D.EditAt ε (.decision j) a b) : SingleGrade a.profile b.profile j := by
  have hn := (D.readouts_decision_eq_iff a b j).not.mp h.2
  rcases D.grade_change_of_step (D.editAt_step h) with he | ⟨_,i,hi⟩
  · exact (hn (congrFun he j)).elim
  · have hji : j = i := by
      by_contra hne
      exact hn (hi.2 j hne)
    exact hji ▸ hi

theorem editAt_preserves_other_grade {ε : ℚ} {p : EditPosition n} {a b : D.protocol.State n}
    (h : D.EditAt ε p a b) (j : Fin (n+1)) (hn : p ≠ .decision j) :
    a.profile.grades j = b.profile.grades j := by
  cases p with
  | decision i =>
    exact (D.editAt_decision_singleGrade h).2 j (fun hji => hn (congrArg EditPosition.decision hji.symm))
  | localLaw =>
    rcases D.grade_change_of_step (D.editAt_step h) with he | ⟨he,_⟩
    · exact congrFun he j
    · simp [EditPosition.effect] at he
  | support =>
    rcases D.grade_change_of_step (D.editAt_step h) with he | ⟨he,_⟩
    · exact congrFun he j
    · simp [EditPosition.effect] at he
  | license =>
    rcases D.grade_change_of_step (D.editAt_step h) with he | ⟨he,_⟩
    · exact congrFun he j
    · simp [EditPosition.effect] at he
  | receipt =>
    rcases D.grade_change_of_step (D.editAt_step h) with he | ⟨he,_⟩
    · exact congrFun he j
    · simp [EditPosition.effect] at he

theorem terminal_decision_changes_iff {ε : ℚ} {p : EditPosition n} {a b : D.protocol.State n}
    (h : D.EditAt ε p a b) :
    (D.readouts a).decision (Fin.last n) ≠ (D.readouts b).decision (Fin.last n) ↔
      p = .decision (Fin.last n) := by
  constructor
  · intro hd
    by_contra hn
    exact hd ((D.readouts_decision_eq_iff a b _).mpr
      (D.editAt_preserves_other_grade h _ hn))
  · rintro rfl
    exact h.2

omit [Nonempty X] [Nonempty R] in
theorem editAt_under_equivalent_presentations {A B : Type*}
    (first : A → D.protocol.State n) (second : B → D.protocol.State n) (translate : A ≃ B)
    (agree : ∀ u, D.readouts (first u) = D.readouts (second (translate u)))
    (ε : ℚ) (p : EditPosition n) (u v : A) :
    D.EditAt ε p (first u) (first v) ↔
      D.EditAt ε p (second (translate u)) (second (translate v)) := by
  change NativeReadouts.editAt (D.attained n) ε p (D.readouts (first u)) (D.readouts (first v)) ↔ _
  rw [agree u,agree v]

theorem editAt_decision_iff_write (ε : ℚ) (j : Fin (n+1)) (a b : D.protocol.State n) :
    D.EditAt ε (.decision j) a b ↔
      (D.readouts a).decision j ≠ (D.readouts b).decision j ∧
      D.readouts b = (D.readouts a).writeDecision j ((D.readouts b).decision j) ∧
      NativeReadouts.cover (D.attained n) (D.readouts a) (D.readouts b) := by
  constructor
  · intro h
    have hs := D.editAt_decision_singleGrade h
    have hc : D.protocol.CapCover a.profile b.profile ∧ a.law = b.law ∧
        a.profile.licenses = b.profile.licenses ∧ a.profile.published = b.profile.published := by
      have hh := D.editAt_step h
      by_cases hj : j = Fin.last n
      · have hl : D.protocol.Step ε .terminal a b := by
          simpa only [EditPosition.effect, if_pos hj] using hh
        exact ⟨hl.1,hl.2.2,hl.2.1.2.1,hl.2.1.2.2.1⟩
      · have hl : D.protocol.Step ε .earlier a b := by
          simpa only [EditPosition.effect, if_neg hj] using hh
        exact ⟨hl.1,hl.2.2,hl.2.1.2.1,hl.2.1.2.2.1⟩
    refine ⟨h.2,?_,(D.readouts_cover_iff a b).mpr hc.1⟩
    apply NativeReadouts.ext
    · exact congrArg (fun law => law.marked D.parity) hc.2.1.symm
    · funext k
      change (D.readouts b).decision k = Function.update (D.readouts a).decision j
        ((D.readouts b).decision j) k
      by_cases hk : k = j
      · subst k
        rw [Function.update_self]
      · rw [Function.update_of_ne hk]
        exact ((D.readouts_decision_eq_iff a b k).mpr (hs.2 k hk)).symm
    · exact congrArg (fun s : Finset Γ => fun g => g ∈ s) hc.2.2.1.symm
    · exact congrArg (fun s : Finset Δ => fun g => g ∈ s) hc.2.2.2.symm
  · rintro ⟨hn,hw,hc⟩
    have hl : (D.readouts a).trial = (D.readouts b).trial :=
      (congrArg NativeReadouts.trial hw).symm
    have hs : (D.readouts a).support = (D.readouts b).support := by
      ext p
      simp [NativeReadouts.support,NativeReadouts.occurs,hl]
    exact ⟨Or.inr ⟨hc,fun _ => hl,fun h => (h hs).elim⟩,hn⟩

theorem editAt_unique {ε : ℚ} {p q : EditPosition n} {a b : D.protocol.State n}
    (hp : D.EditAt ε p a b) (hq : D.EditAt ε q a b) : p = q := by
  have he : p.effect = q.effect := by
    have h := (D.typed_edit_iff_step _ _ _ _).mpr (D.editAt_step hp)
    exact (D.detected_iff_label (D.editAt_step hq) _).mp h.2
  cases p <;> cases q
  case decision.decision i j =>
    by_contra hn
    have hj := (D.readouts_decision_eq_iff a b j).not.mp hq.2
    exact hj (D.editAt_preserves_other_grade hp j hn)
  all_goals try rfl
  all_goals simp only [EditPosition.effect, reduceCtorEq] at he
  all_goals split at he <;> contradiction

end NativeExperiments
end MovingProjection
