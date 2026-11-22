import MovingProjection.PrimitiveCommands

/-! Completeness and irredundancy of catalogues of uniform native commands. -/

namespace MovingProjection

/-- One native command and its declared parameter domain. The timed decision
command may be specialized to a state-independent set of clock grades. -/
inductive PrimitiveFamily (n : ℕ)
  | localLaw
  | support
  | disclose (grades : Finset (Fin (n+1)))
  | license
  | receipt
  deriving DecidableEq

def PrimitiveFamily.positions {n : ℕ} : PrimitiveFamily n → Set (EditPosition n)
  | .localLaw => {p | p = .localLaw}
  | .support => {p | p = .support}
  | .disclose grades => {p | ∃ j ∈ grades, p = .decision j}
  | .license => {p | p = .license}
  | .receipt => {p | p = .receipt}

def offeredPositions {n : ℕ} (basis : Finset (PrimitiveFamily n)) : Set (EditPosition n) :=
  {p | ∃ f ∈ basis, p ∈ f.positions}

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I] [Nonempty X] [Nonempty R]
  (D : NativeExperiments M I X R Γ Δ)

abbrev OfferedEdit (ε : ℚ) (positions : Set (EditPosition n)) (a b : D.protocol.State n) : Prop :=
  ∃ p ∈ positions, D.EditAt ε p a b

abbrev Generated (ε : ℚ) (positions : Set (EditPosition n)) (a b : D.protocol.State n) : Prop :=
  Relation.ReflTransGen (D.OfferedEdit ε positions) a b

def Live (ε : ℚ) (p : EditPosition n) : Prop :=
  ∃ a b : D.protocol.State n, a ≠ b ∧ D.EditAt ε p a b

def Complete (ε : ℚ) (positions : Set (EditPosition n)) : Prop :=
  ∀ a b : D.protocol.State n, D.protocol.Chain ε a b → D.Generated ε positions a b

def IsBasis (ε : ℚ) (basis : Finset (PrimitiveFamily n)) : Prop :=
  D.Complete ε (offeredPositions basis) ∧
    ∀ f ∈ basis, ¬ D.Complete ε (offeredPositions (basis.erase f))

theorem generated_is_native {ε : ℚ} {positions : Set (EditPosition n)}
    {a b : D.protocol.State n} (h : D.Generated ε positions a b) :
    D.protocol.Chain ε a b :=
  h.mono fun _ _ ⟨p,_,hp⟩ => ⟨p.effect,D.editAt_step hp⟩

private theorem generated_omits_effect {ε : ℚ} {positions : Set (EditPosition n)}
    {p : EditPosition n} {a b : D.protocol.State n} (h : D.Generated ε positions a b)
    (hp : p ∉ positions) (hunique : ∀ q : EditPosition n, q.effect = p.effect → q = p) :
    D.protocol.Omitting p.effect ε a b :=
  h.mono fun _ _ ⟨q,hq,hs⟩ =>
    ⟨q.effect,fun he => hp (hunique q he ▸ hq),D.editAt_step hs⟩

theorem generated_preserves_missing_grade {ε : ℚ} {positions : Set (EditPosition n)}
    {a b : D.protocol.State n} (h : D.Generated ε positions a b) {j : Fin (n+1)}
    (hm : EditPosition.decision j ∉ positions) :
    a.profile.grades j = b.profile.grades j := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨p,hp,he⟩ := hs
    exact ih.trans (D.editAt_preserves_other_grade he j (fun hEq => hm (hEq ▸ hp)))

/-- An observed, nonidentity invocation cannot be simulated by commands
which omit its position. Support monotonicity handles fixed-support laws
even when their projected marginals happen to agree. -/
theorem missing_position_blocks {ε : ℚ} {positions : Set (EditPosition n)}
    {p : EditPosition n} {a b : D.protocol.State n}
    (hm : p ∉ positions) (hne : a ≠ b) (h : D.EditAt ε p a b) :
    ¬ D.Generated ε positions a b := by
  intro chain
  cases p with
  | localLaw =>
    have ho := D.generated_omits_effect chain hm
      (fun q hq => (EditPosition.effect_eq_rewrite q).mp hq)
    have hEq : a.profile = b.profile := (show
      a.profile = b.profile ∧ PhysicalNear D.parity ε a.law b.law from D.editAt_step h).1
    exact hne (Protocol.State.ext hEq (ho.law (congrArg Capabilities.mask hEq)))
  | support =>
    have ho := D.generated_omits_effect chain hm
      (fun q hq => (EditPosition.effect_eq_gate q).mp hq)
    have hEq : (D.readouts a).support = (D.readouts b).support := by
      rw [D.readouts_support, D.readouts_support, ho.support]
    exact h.2 hEq
  | license =>
    have ho := D.generated_omits_effect chain hm
      (fun q hq => (EditPosition.effect_eq_route q).mp hq)
    exact h.2 (congrArg (fun s : Finset Γ => fun g => g ∈ s) ho.licenses)
  | receipt =>
    have ho := D.generated_omits_effect chain hm
      (fun q hq => (EditPosition.effect_eq_publication q).mp hq)
    exact h.2 (congrArg (fun s : Finset Δ => fun g => g ∈ s) ho.citations)
  | decision j =>
    exact h.2 ((D.readouts_decision_eq_iff a b j).mpr
      (D.generated_preserves_missing_grade chain hm))

theorem complete_iff_live (ε : ℚ) (positions : Set (EditPosition n)) :
    D.Complete ε positions ↔ ∀ p, D.Live ε p → p ∈ positions := by
  constructor
  · intro h p hp
    obtain ⟨a,b,hne,he⟩ := hp
    by_contra hm
    exact D.missing_position_blocks hm hne he
      (h a b (.single ⟨p.effect,D.editAt_step he⟩))
  · intro h a b chain
    induction chain with
    | refl => exact .refl
    | @tail x y hx hs ih =>
      obtain ⟨e,he⟩ := hs
      obtain ⟨p,_,hp⟩ := D.step_iff_editAt.mp he
      by_cases hxy : x = y
      · exact hxy ▸ ih
      · exact ih.tail ⟨p,h p ⟨x,y,hxy,hp⟩,hp⟩

/-- Coverage and essentiality are both determined by live native positions.
An essential family has a live position which no remaining family offers. -/
theorem isBasis_iff (ε : ℚ) (basis : Finset (PrimitiveFamily n)) :
    D.IsBasis ε basis ↔
      (∀ p, D.Live ε p → p ∈ offeredPositions basis) ∧
      (∀ f ∈ basis, ∃ p, D.Live ε p ∧ p ∈ f.positions ∧
        p ∉ offeredPositions (basis.erase f)) := by
  classical
  constructor
  · rintro ⟨hc,hm⟩
    have hl := (D.complete_iff_live ε _).mp hc
    refine ⟨hl,?_⟩
    intro f hf
    have hn : ¬ ∀ p, D.Live ε p → p ∈ offeredPositions (basis.erase f) :=
      fun H => hm f hf ((D.complete_iff_live ε _).mpr H)
    push_neg at hn
    obtain ⟨p,hp,hn⟩ := hn
    obtain ⟨g,hg,hpos⟩ := hl p hp
    have hEq : g = f := by
      by_contra hgf
      exact hn ⟨g,Finset.mem_erase.mpr ⟨hgf,hg⟩,hpos⟩
    exact ⟨p,hp,hEq ▸ hpos,hn⟩
  · rintro ⟨hc,hm⟩
    refine ⟨(D.complete_iff_live ε _).mpr hc,?_⟩
    intro f hf h
    obtain ⟨p,hp,_,hn⟩ := hm f hf
    exact hn ((D.complete_iff_live ε _).mp h p hp)

theorem offeredEdit_of_covers_all (ε : ℚ) (positions : Set (EditPosition n))
    (h : ∀ p, p ∈ positions) (a b : D.protocol.State n) :
    D.OfferedEdit ε positions a b ↔
      NativeReadouts.elementary (D.attained n) ε (D.readouts a) (D.readouts b) := by
  constructor
  · rintro ⟨_,_,he⟩
    exact he.1
  · intro he
    obtain ⟨e,hs⟩ := (D.elementary_iff_step ε a b).mp he
    obtain ⟨p,_,hp⟩ := D.step_iff_editAt.mp hs
    exact ⟨p,h p,hp⟩

end NativeExperiments
end MovingProjection
