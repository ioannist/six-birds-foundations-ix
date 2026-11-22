import MovingProjection.FamilyBasis
import MovingProjection.RealizesRoles

/-! Two descriptions of the same native edit language, with different
numbers of essential command families. -/

namespace MovingProjection
namespace PrimitiveFamily

def withoutClock (n : ℕ) : Finset (PrimitiveFamily n) :=
  {.localLaw,.support,.license,.receipt}

def uniformClock (n : ℕ) : Finset (PrimitiveFamily n) :=
  insert (.disclose Finset.univ) (withoutClock n)

def splitClock (n : ℕ) : Finset (PrimitiveFamily n) :=
  insert (.disclose (Finset.univ.erase (Fin.last n)))
    (insert (.disclose {Fin.last n}) (withoutClock n))

@[simp] theorem localLaw_mem_positions {n : ℕ} (f : PrimitiveFamily n) :
    .localLaw ∈ f.positions ↔ f = .localLaw := by
  cases f <;> simp [positions]

@[simp] theorem support_mem_positions {n : ℕ} (f : PrimitiveFamily n) :
    .support ∈ f.positions ↔ f = .support := by
  cases f <;> simp [positions]

@[simp] theorem license_mem_positions {n : ℕ} (f : PrimitiveFamily n) :
    .license ∈ f.positions ↔ f = .license := by
  cases f <;> simp [positions]

@[simp] theorem receipt_mem_positions {n : ℕ} (f : PrimitiveFamily n) :
    .receipt ∈ f.positions ↔ f = .receipt := by
  cases f <;> simp [positions]

@[simp] theorem decision_mem_positions {n : ℕ} (j : Fin (n+1)) (f : PrimitiveFamily n) :
    .decision j ∈ f.positions ↔ ∃ grades, j ∈ grades ∧ f = .disclose grades := by
  cases f <;> simp [positions]

theorem withoutClock_subset_uniform (n : ℕ) : withoutClock n ⊆ uniformClock n := by
  intro x hx
  exact Finset.mem_insert_of_mem hx

theorem withoutClock_subset_split (n : ℕ) : withoutClock n ⊆ splitClock n := by
  intro x hx
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)

private theorem withoutClock_offers_nondecision {n : ℕ} {catalogue : Finset (PrimitiveFamily n)}
    (h : withoutClock n ⊆ catalogue) (p : EditPosition n) (hp : ∀ j, p ≠ .decision j) :
    p ∈ offeredPositions catalogue := by
  cases p with
  | decision j => exact (hp j rfl).elim
  | localLaw => exact ⟨.localLaw,h (by simp [withoutClock]),rfl⟩
  | support => exact ⟨.support,h (by simp [withoutClock]),rfl⟩
  | license => exact ⟨.license,h (by simp [withoutClock]),rfl⟩
  | receipt => exact ⟨.receipt,h (by simp [withoutClock]),rfl⟩

theorem uniformClock_offers_all {n : ℕ} (p : EditPosition n) :
    p ∈ offeredPositions (uniformClock n) := by
  by_cases hp : ∃ j, p = .decision j
  · obtain ⟨j,rfl⟩ := hp
    exact ⟨.disclose Finset.univ,Finset.mem_insert_self _ _,j,Finset.mem_univ _,rfl⟩
  · exact withoutClock_offers_nondecision (withoutClock_subset_uniform n) p
      (fun j h => hp ⟨j,h⟩)

theorem splitClock_offers_all {n : ℕ} (p : EditPosition n) :
    p ∈ offeredPositions (splitClock n) := by
  by_cases hp : ∃ j, p = .decision j
  · obtain ⟨j,rfl⟩ := hp
    by_cases hj : j = Fin.last n
    · subst j
      exact ⟨.disclose {Fin.last n},Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
        Fin.last n,Finset.mem_singleton_self _,rfl⟩
    · exact ⟨.disclose (Finset.univ.erase (Fin.last n)),Finset.mem_insert_self _ _,
        j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩,rfl⟩
  · exact withoutClock_offers_nondecision (withoutClock_subset_split n) p
      (fun j h => hp ⟨j,h⟩)

theorem uniformClock_card (n : ℕ) : (uniformClock n).card = 5 := by
  simp [uniformClock,withoutClock,Finset.card_insert_of_notMem]

theorem splitClock_card_two_grades : (splitClock 1).card = 6 := by
  decide

theorem splitClock_two_grades : splitClock 1 =
    insert (.disclose {0}) (insert (.disclose {1}) (withoutClock 1)) := by
  decide

theorem mem_withoutClock_iff {n : ℕ} (f : PrimitiveFamily n) :
    f ∈ withoutClock n ↔ ∀ grades, f ≠ .disclose grades := by
  cases f <;> simp [withoutClock]

theorem withoutClock_of_offers_all {n : ℕ} {catalogue : Finset (PrimitiveFamily n)}
    (h : ∀ p, p ∈ offeredPositions catalogue) : withoutClock n ⊆ catalogue := by
  intro f hf
  have hclock := (mem_withoutClock_iff f).mp hf
  cases f with
  | localLaw => simpa [offeredPositions] using h .localLaw
  | support => simpa [offeredPositions] using h .support
  | license => simpa [offeredPositions] using h .license
  | receipt => simpa [offeredPositions] using h .receipt
  | disclose grades => exact (hclock grades rfl).elim

theorem uniformClock_unique_owner {n : ℕ} {p : EditPosition n} {f g : PrimitiveFamily n}
    (hf : f ∈ uniformClock n) (hg : g ∈ uniformClock n)
    (hfp : p ∈ f.positions) (hgp : p ∈ g.positions) : f = g := by
  cases p with
  | localLaw => exact (localLaw_mem_positions f).mp hfp |>.trans ((localLaw_mem_positions g).mp hgp).symm
  | support => exact (support_mem_positions f).mp hfp |>.trans ((support_mem_positions g).mp hgp).symm
  | license => exact (license_mem_positions f).mp hfp |>.trans ((license_mem_positions g).mp hgp).symm
  | receipt => exact (receipt_mem_positions f).mp hfp |>.trans ((receipt_mem_positions g).mp hgp).symm
  | decision j =>
    obtain ⟨s,_,rfl⟩ := (decision_mem_positions j f).mp hfp
    obtain ⟨t,_,rfl⟩ := (decision_mem_positions j g).mp hgp
    simp [uniformClock,withoutClock] at hf hg
    rw [hf,hg]

theorem splitClock_unique_owner {n : ℕ} {p : EditPosition n} {f g : PrimitiveFamily n}
    (hf : f ∈ splitClock n) (hg : g ∈ splitClock n)
    (hfp : p ∈ f.positions) (hgp : p ∈ g.positions) : f = g := by
  cases p with
  | localLaw => exact (localLaw_mem_positions f).mp hfp |>.trans ((localLaw_mem_positions g).mp hgp).symm
  | support => exact (support_mem_positions f).mp hfp |>.trans ((support_mem_positions g).mp hgp).symm
  | license => exact (license_mem_positions f).mp hfp |>.trans ((license_mem_positions g).mp hgp).symm
  | receipt => exact (receipt_mem_positions f).mp hfp |>.trans ((receipt_mem_positions g).mp hgp).symm
  | decision j =>
    obtain ⟨s,hs,rfl⟩ := (decision_mem_positions j f).mp hfp
    obtain ⟨t,ht,rfl⟩ := (decision_mem_positions j g).mp hgp
    simp [splitClock,withoutClock] at hf hg
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
    · rfl
    · exact ((Finset.mem_erase.mp hs).1 (Finset.mem_singleton.mp ht)).elim
    · exact ((Finset.mem_erase.mp ht).1 (Finset.mem_singleton.mp hs)).elim
    · rfl

/-- A command invocation retains the site parameter independently of the
family which supplies the command. -/
def Invocation {n : ℕ} (catalogue : Finset (PrimitiveFamily n)) :=
  {q : PrimitiveFamily n × EditPosition n // q.1 ∈ catalogue ∧ q.2 ∈ q.1.positions}

noncomputable def invocationPositions {n : ℕ} (catalogue : Finset (PrimitiveFamily n))
    (covers : ∀ p, p ∈ offeredPositions catalogue)
    (unique : ∀ {p f g}, f ∈ catalogue → g ∈ catalogue →
      p ∈ f.positions → p ∈ g.positions → f = g) : Invocation catalogue ≃ EditPosition n :=
  Equiv.ofBijective (fun q => q.val.2) (by
    constructor
    · rintro ⟨⟨f,p⟩,hf,hfp⟩ ⟨⟨g,q⟩,hg,hgq⟩ hpq
      change p = q at hpq
      subst q
      exact Subtype.ext (Prod.ext (unique hf hg hfp hgq) rfl)
    · intro p
      obtain ⟨f,hf,hp⟩ := covers p
      exact ⟨⟨(f,p),hf,hp⟩,rfl⟩)

noncomputable def reparameterizeClock (n : ℕ) : Invocation (uniformClock n) ≃ Invocation (splitClock n) :=
  (invocationPositions _ uniformClock_offers_all uniformClock_unique_owner).trans
    (invocationPositions _ splitClock_offers_all splitClock_unique_owner).symm

theorem reparameterizeClock_preserves_position {n : ℕ} (q : Invocation (uniformClock n)) :
    ((reparameterizeClock n) q).val.2 = q.val.2 :=
  (invocationPositions _ splitClock_offers_all splitClock_unique_owner).apply_symm_apply q.val.2

end PrimitiveFamily

namespace NativeExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq M] [DecidableEq I] [Nonempty X] [Nonempty R]
  (D : NativeExperiments M I X R Γ Δ)

theorem uniform_and_split_same_elementary_edits (ε : ℚ) (a b : D.protocol.State n) :
    D.OfferedEdit ε (offeredPositions (PrimitiveFamily.uniformClock n)) a b ↔
      D.OfferedEdit ε (offeredPositions (PrimitiveFamily.splitClock n)) a b :=
  (D.offeredEdit_of_covers_all ε _ PrimitiveFamily.uniformClock_offers_all a b).trans
    (D.offeredEdit_of_covers_all ε _ PrimitiveFamily.splitClock_offers_all a b).symm

omit [Nonempty X] [Nonempty R] in
theorem reparameterized_invocation_iff (q : PrimitiveFamily.Invocation (PrimitiveFamily.uniformClock n))
    (ε : ℚ) (a b : D.protocol.State n) :
    D.EditAt ε ((PrimitiveFamily.reparameterizeClock n) q).val.2 a b ↔
      D.EditAt ε q.val.2 a b := by
  rw [PrimitiveFamily.reparameterizeClock_preserves_position]

theorem uniform_clock_chain_iff (ε : ℚ) (a b : D.protocol.State n) :
    D.Generated ε (offeredPositions (PrimitiveFamily.uniformClock n)) a b ↔
      D.protocol.Chain ε a b :=
  ⟨D.generated_is_native, (D.complete_iff_live ε _).mpr
    (fun p _ => PrimitiveFamily.uniformClock_offers_all p) a b⟩

theorem split_clock_chain_iff (ε : ℚ) (a b : D.protocol.State n) :
    D.Generated ε (offeredPositions (PrimitiveFamily.splitClock n)) a b ↔
      D.protocol.Chain ε a b :=
  ⟨D.generated_is_native, (D.complete_iff_live ε _).mpr
    (fun p _ => PrimitiveFamily.splitClock_offers_all p) a b⟩

/-- An additional interface contract a client could require. The family
name alone determines whether a successful call changes the terminal
decision readout, independently of its arguments. -/
def TerminalHomogeneous (ε : ℚ) (catalogue : Finset (PrimitiveFamily n)) : Prop :=
  ∀ f ∈ catalogue, ∀ p ∈ f.positions, ∀ q ∈ f.positions,
    ∀ a b u v : D.protocol.State n, D.EditAt ε p a b → D.EditAt ε q u v →
      ((D.readouts a).decision (Fin.last n) ≠ (D.readouts b).decision (Fin.last n) ↔
       (D.readouts u).decision (Fin.last n) ≠ (D.readouts v).decision (Fin.last n))

theorem splitClock_terminal_homogeneous (ε : ℚ) :
    D.TerminalHomogeneous ε (PrimitiveFamily.splitClock n) := by
  intro f hf p hp q hq a b u v hu hv
  rw [D.terminal_decision_changes_iff hu, D.terminal_decision_changes_iff hv]
  have terminal (p q : EditPosition n) (hp : p ∈ f.positions) (hq : q ∈ f.positions)
      (h : p = .decision (Fin.last n)) : q = .decision (Fin.last n) := by
    subst p
    have hf' : f = .disclose {Fin.last n} := PrimitiveFamily.splitClock_unique_owner
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) hp
        ⟨Fin.last n,Finset.mem_singleton_self _,rfl⟩
    subst f
    obtain ⟨j,hj,hq⟩ := hq
    exact hq.trans (congrArg EditPosition.decision (Finset.mem_singleton.mp hj))
  exact ⟨terminal p q hp hq, terminal q p hq hp⟩

end NativeExperiments

namespace Example

private def positionOfEffect : Effect → EditPosition 1
  | .rewrite => .localLaw
  | .gate => .support
  | .route => .license
  | .earlier => .decision 0
  | .terminal => .decision 1
  | .publication => .receipt

private theorem effect_injective_two_grades :
    Function.Injective (fun p : EditPosition 1 => p.effect) := by
  apply Function.LeftInverse.injective (g := positionOfEffect)
  intro p
  cases p with
  | decision j => fin_cases j <;> rfl
  | localLaw => rfl
  | support => rfl
  | license => rfl
  | receipt => rfl

theorem every_position_live (ε : ℚ) (hε : 0 < ε) (p : EditPosition 1) : experiment.Live ε p := by
  obtain ⟨a,b,hne,he⟩ := Manuscript.every_effect_occurs (Manuscript.roleEquiv.symm p.effect) ε hε
  have hs := (experiment.typed_edit_iff_step _ _ _ _).mp he
  have hp : Manuscript.effect (Manuscript.roleEquiv.symm p.effect) = p.effect :=
    Manuscript.roleEquiv.apply_symm_apply p.effect
  rw [hp] at hs
  obtain ⟨q,hq,h⟩ := experiment.step_iff_editAt.mp hs
  exact ⟨a,b,hne,effect_injective_two_grades hq ▸ h⟩

private theorem offered_by_no_other {catalogue : Finset (PrimitiveFamily 1)}
    {f : PrimitiveFamily 1} {p : EditPosition 1}
    (h : ∀ g ∈ catalogue, p ∈ g.positions → g = f) :
    p ∉ offeredPositions (catalogue.erase f) := by
  rintro ⟨g,hg,hp⟩
  obtain ⟨hne,hg⟩ := Finset.mem_erase.mp hg
  exact hne (h g hg hp)

private theorem clock_has_private_position {catalogue : Finset (PrimitiveFamily 1)}
    (h : ∀ f ∈ catalogue, ∀ grades, f = .disclose grades →
      ∃ j ∈ grades, (.decision j : EditPosition 1) ∉ offeredPositions (catalogue.erase f)) :
    ∀ f ∈ catalogue, ∃ p : EditPosition 1, p ∈ f.positions ∧
      p ∉ offeredPositions (catalogue.erase f) := by
  intro f hf
  cases f with
  | disclose grades =>
    obtain ⟨j,hj,hn⟩ := h (.disclose grades) hf grades rfl
    exact ⟨.decision j,⟨j,hj,rfl⟩,hn⟩
  | localLaw =>
    exact ⟨.localLaw,rfl,offered_by_no_other (fun g _ hp => (PrimitiveFamily.localLaw_mem_positions g).mp hp)⟩
  | support =>
    exact ⟨.support,rfl,offered_by_no_other (fun g _ hp => (PrimitiveFamily.support_mem_positions g).mp hp)⟩
  | license =>
    exact ⟨.license,rfl,offered_by_no_other (fun g _ hp => (PrimitiveFamily.license_mem_positions g).mp hp)⟩
  | receipt =>
    exact ⟨.receipt,rfl,offered_by_no_other (fun g _ hp => (PrimitiveFamily.receipt_mem_positions g).mp hp)⟩

private theorem basis_of_private_positions (ε : ℚ) (hε : 0 < ε) (catalogue : Finset (PrimitiveFamily 1))
    (hc : ∀ p, p ∈ offeredPositions catalogue)
    (hm : ∀ f ∈ catalogue, ∃ p : EditPosition 1, p ∈ f.positions ∧
      p ∉ offeredPositions (catalogue.erase f)) :
    experiment.IsBasis ε catalogue := by
  apply (experiment.isBasis_iff ε _).mpr
  refine ⟨fun p _ => hc p,?_⟩
  intro f hf
  obtain ⟨p,hp,hn⟩ := hm f hf
  exact ⟨p,every_position_live ε hε p,hp,hn⟩

theorem uniformClock_isBasis (ε : ℚ) (hε : 0 < ε) :
    experiment.IsBasis ε (PrimitiveFamily.uniformClock 1) := by
  apply basis_of_private_positions ε hε _ PrimitiveFamily.uniformClock_offers_all
  apply clock_has_private_position
  rintro _ hf grades rfl
  have hg : grades = Finset.univ := by
    simpa [PrimitiveFamily.uniformClock,PrimitiveFamily.withoutClock] using hf
  subst grades
  refine ⟨0,Finset.mem_univ _,offered_by_no_other ?_⟩
  intro g hg hp
  obtain ⟨grades,_,rfl⟩ := (PrimitiveFamily.decision_mem_positions 0 g).mp hp
  simpa [PrimitiveFamily.uniformClock,PrimitiveFamily.withoutClock] using hg

theorem splitClock_isBasis (ε : ℚ) (hε : 0 < ε) :
    experiment.IsBasis ε (PrimitiveFamily.splitClock 1) := by
  apply basis_of_private_positions ε hε _ PrimitiveFamily.splitClock_offers_all
  apply clock_has_private_position
  rintro _ hf grades rfl
  have hg : grades = {0} ∨ grades = {1} := by
    simpa [PrimitiveFamily.splitClock_two_grades,PrimitiveFamily.withoutClock] using hf
  have alone (j : Fin 2) (g : PrimitiveFamily 1) (hg : g ∈ PrimitiveFamily.splitClock 1)
      (hp : .decision j ∈ g.positions) : g = .disclose {j} := by
    obtain ⟨s,hs,rfl⟩ := (PrimitiveFamily.decision_mem_positions j g).mp hp
    have hh : s = {0} ∨ s = {1} := by
      simpa [PrimitiveFamily.splitClock_two_grades,PrimitiveFamily.withoutClock] using hg
    rcases hh with rfl | rfl <;>
      obtain rfl := Finset.mem_singleton.mp hs <;> rfl
  rcases hg with rfl | rfl
  · exact ⟨0,Finset.mem_singleton_self _,offered_by_no_other (alone 0)⟩
  · exact ⟨1,Finset.mem_singleton_self _,offered_by_no_other (alone 1)⟩

private theorem proper_grade_domain {grades : Finset (Fin 2)} {j : Fin 2}
    (hj : j ∈ grades) (hne : grades ≠ Finset.univ) : grades = {j} := by
  have hs : ({j} : Finset (Fin 2)) ⊆ grades := Finset.singleton_subset_iff.mpr hj
  have hcard : grades.card < 2 := by
    have hl := Finset.card_lt_card (ssubset_of_subset_of_ne (Finset.subset_univ grades) hne)
    simpa using hl
  have hle : grades.card ≤ ({j} : Finset (Fin 2)).card := by
    simpa using Nat.le_of_lt_succ hcard
  exact (Finset.eq_of_subset_of_card_le hs hle).symm

/-- Exhaust the possible bases on the same coupled two-grade source.
Single-field commands can group the two live grades or offer them separately. -/
theorem every_basis_two_grades (ε : ℚ) (hε : 0 < ε) (catalogue : Finset (PrimitiveFamily 1)) :
    experiment.IsBasis ε catalogue ↔
      catalogue = PrimitiveFamily.uniformClock 1 ∨ catalogue = PrimitiveFamily.splitClock 1 := by
  classical
  constructor
  · intro h
    obtain ⟨hc,hm⟩ := (experiment.isBasis_iff ε catalogue).mp h
    have hAll (p : EditPosition 1) := hc p (every_position_live ε hε p)
    have hfixed := PrimitiveFamily.withoutClock_of_offers_all hAll
    have privateClock {s : Finset (Fin 2)} (hs : PrimitiveFamily.disclose s ∈ catalogue) :
        ∃ j ∈ s, (.decision j : EditPosition 1) ∉ offeredPositions (catalogue.erase (.disclose s)) := by
      obtain ⟨p,_,hp,hn⟩ := hm (.disclose s) hs
      obtain ⟨j,hj,rfl⟩ := hp
      exact ⟨j,hj,hn⟩
    by_cases hfull : PrimitiveFamily.disclose Finset.univ ∈ catalogue
    · apply Or.inl
      apply Finset.Subset.antisymm
      · intro f hf
        by_cases hd : ∃ s, f = PrimitiveFamily.disclose s
        · obtain ⟨s,rfl⟩ := hd
          by_cases heq : s = Finset.univ
          · subst s
            exact Finset.mem_insert_self _ _
          · obtain ⟨j,_,hn⟩ := privateClock hf
            exact (hn ⟨.disclose Finset.univ,Finset.mem_erase.mpr
              ⟨fun hh => heq (PrimitiveFamily.disclose.inj hh).symm,hfull⟩,
              j,Finset.mem_univ _,rfl⟩).elim
        · exact PrimitiveFamily.withoutClock_subset_uniform 1
            ((PrimitiveFamily.mem_withoutClock_iff f).mpr (fun s hs => hd ⟨s,hs⟩))
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hmem
        · exact hfull
        · exact hfixed hmem
    · apply Or.inr
      rw [PrimitiveFamily.splitClock_two_grades]
      apply Finset.Subset.antisymm
      · intro f hf
        by_cases hd : ∃ s, f = PrimitiveFamily.disclose s
        · obtain ⟨s,rfl⟩ := hd
          obtain ⟨j,hj,_⟩ := privateClock hf
          have heq := proper_grade_domain hj (fun heq => hfull (heq ▸ hf))
          subst s
          fin_cases j
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            ((PrimitiveFamily.mem_withoutClock_iff f).mpr (fun s hs => hd ⟨s,hs⟩)))
      · have each (j : Fin 2) : PrimitiveFamily.disclose {j} ∈ catalogue := by
          obtain ⟨f,hf,hp⟩ := hAll (.decision j)
          obtain ⟨s,hs,rfl⟩ := (PrimitiveFamily.decision_mem_positions j f).mp hp
          have heq := proper_grade_domain hs (fun heq => hfull (heq ▸ hf))
          exact heq ▸ hf
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hrest
        · exact each 0
        rcases Finset.mem_insert.mp hrest with rfl | hmem
        · exact each 1
        · exact hfixed hmem
  · rintro (rfl | rfl)
    · exact uniformClock_isBasis ε hε
    · exact splitClock_isBasis ε hε

theorem five_and_six_both_irredundant (ε : ℚ) (hε : 0 < ε) :
    experiment.IsBasis ε (PrimitiveFamily.uniformClock 1) ∧
      experiment.IsBasis ε (PrimitiveFamily.splitClock 1) ∧
      (PrimitiveFamily.uniformClock 1).card = 5 ∧ (PrimitiveFamily.splitClock 1).card = 6 :=
  ⟨uniformClock_isBasis ε hε,splitClock_isBasis ε hε,
    PrimitiveFamily.uniformClock_card 1,PrimitiveFamily.splitClock_card_two_grades⟩

theorem minimum_complete_catalogue (ε : ℚ) (hε : 0 < ε)
    {catalogue : Finset (PrimitiveFamily 1)}
    (hc : experiment.Complete ε (offeredPositions catalogue)) :
    5 ≤ catalogue.card ∧ (catalogue.card = 5 ↔ catalogue = PrimitiveFamily.uniformClock 1) := by
  have lower (B : Finset (PrimitiveFamily 1))
      (hB : experiment.Complete ε (offeredPositions B)) : 5 ≤ B.card := by
    have hall (p : EditPosition 1) :=
      (experiment.complete_iff_live ε _).mp hB p (every_position_live ε hε p)
    obtain ⟨f,hf,hp⟩ := hall (.decision 0)
    obtain ⟨s,_,rfl⟩ := (PrimitiveFamily.decision_mem_positions 0 f).mp hp
    have hs : insert (.disclose s) (PrimitiveFamily.withoutClock 1) ⊆ B :=
      Finset.insert_subset_iff.mpr ⟨hf,PrimitiveFamily.withoutClock_of_offers_all hall⟩
    simpa [PrimitiveFamily.withoutClock,Finset.card_insert_of_notMem] using Finset.card_le_card hs
  refine ⟨lower catalogue hc,?_⟩
  constructor
  · intro hfive
    have hb : experiment.IsBasis ε catalogue := by
      refine ⟨hc,?_⟩
      intro f hf moved
      have hsmall := (lower _ moved).trans_lt (Finset.card_erase_lt_of_mem hf)
      exact (lt_irrefl _) (hfive ▸ hsmall)
    rcases (every_basis_two_grades ε hε catalogue).mp hb with hu | hsix
    · exact hu
    · rw [hsix,PrimitiveFamily.splitClock_card_two_grades] at hfive
      contradiction
  · rintro rfl
    exact PrimitiveFamily.uniformClock_card 1

theorem uniformClock_varies_terminal_contract (ε : ℚ) (hε : 0 < ε) :
    ¬ experiment.TerminalHomogeneous ε (PrimitiveFamily.uniformClock 1) := by
  intro h
  obtain ⟨a,b,_,hab⟩ := every_position_live ε hε (.decision 0)
  obtain ⟨u,v,_,huv⟩ := every_position_live ε hε (.decision 1)
  have H := h (.disclose Finset.univ) (Finset.mem_insert_self _ _) (.decision 0)
    ⟨0,Finset.mem_univ _,rfl⟩ (.decision 1) ⟨1,Finset.mem_univ _,rfl⟩ a b u v hab huv
  rw [experiment.terminal_decision_changes_iff hab,experiment.terminal_decision_changes_iff huv] at H
  exact (by decide : (EditPosition.decision (0 : Fin 2)) ≠ .decision (Fin.last 1)) (H.mpr rfl)

theorem six_with_terminal_contract (ε : ℚ) (hε : 0 < ε) (B : Finset (PrimitiveFamily 1)) :
    (experiment.IsBasis ε B ∧ experiment.TerminalHomogeneous ε B) ↔
      B = PrimitiveFamily.splitClock 1 := by
  constructor
  · rintro ⟨hb,ht⟩
    rcases (every_basis_two_grades ε hε B).mp hb with rfl | he
    · exact (uniformClock_varies_terminal_contract ε hε ht).elim
    · exact he
  · rintro rfl
    exact ⟨splitClock_isBasis ε hε, experiment.splitClock_terminal_homogeneous ε⟩

theorem clock_family_retains_single_grade_limit (ε : ℚ) (hε : 0 < ε) :
    experiment.Generated ε (offeredPositions (PrimitiveFamily.uniformClock 1)) rewritten disclosed ∧
      ¬ experiment.OfferedEdit ε (offeredPositions (PrimitiveFamily.uniformClock 1)) rewritten disclosed := by
  refine ⟨(experiment.uniform_clock_chain_iff ε _ _).mpr
    ((adjacent_factorable .terminal ε hε).trans (adjacent_factorable .earlier ε hε)),?_⟩
  rintro ⟨p,_,h⟩
  have differs (j : Fin 2) :
      (experiment.readouts rewritten).decision j ≠ (experiment.readouts disclosed).decision j := by
    intro he
    have visible : (experiment.readouts disclosed).decision j blockBit := by
      fin_cases j <;> exact blockBit_available
    have inconsistent : (experiment.readouts rewritten).decision j blockBit := by
      rw [he]
      exact visible
    fin_cases j <;> exact blockBit_hidden inconsistent
  have required (j : Fin 2) : p = .decision j := by
    by_contra hn
    exact differs j ((experiment.readouts_decision_eq_iff rewritten disclosed j).mpr
      (experiment.editAt_preserves_other_grade h j hn))
  exact (by decide : (EditPosition.decision (0 : Fin 2)) ≠ .decision 1)
    ((required 0).symm.trans (required 1))

theorem uniform_clock_retains_obstruction :
    ¬ experiment.Generated obstructionTolerance (offeredPositions (PrimitiveFamily.uniformClock 1))
      initial opposite :=
  fun h => obstruction_at_native_tolerance
    ((experiment.uniform_clock_chain_iff _ _ _).mp h)

/-- A test-preserving equivalence of catalogues would in particular induce
a bijection between their families. -/
theorem bases_not_equivalent :
    ¬ Nonempty ((PrimitiveFamily.uniformClock 1) ≃ (PrimitiveFamily.splitClock 1)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  apply (by decide : (5 : ℕ) ≠ 6)
  simpa only [Fintype.card_coe, PrimitiveFamily.uniformClock_card,
    PrimitiveFamily.splitClock_card_two_grades] using h

end Example
end MovingProjection
