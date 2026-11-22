import MovingProjection.Example
import MovingProjection.Readouts

/-! Concrete experimental data for the role certificates on the coupled example. -/

namespace MovingProjection.Example

def blockBit (u : Cell) : Bool := decide (u.val < 2)

theorem blockBit_available : Available bit blockBit := fun _ _ h => h

theorem blockBit_hidden : ¬ Available (⊤ : Setoid Cell) blockBit := by
  intro h
  exact (by decide : blockBit 0 ≠ blockBit 2) (h 0 2 trivial)

theorem earlier_disclosure_changes_timed_test :
    ¬ (experiment.readouts packaged).decision 0 blockBit ∧
    (experiment.readouts disclosed).decision 0 blockBit ∧
    (experiment.readouts packaged).decision 1 = (experiment.readouts disclosed).decision 1 :=
  ⟨blockBit_hidden, blockBit_available, rfl⟩

theorem terminal_packaging_changes_timed_test :
    ¬ (experiment.readouts rewritten).decision 1 blockBit ∧
    (experiment.readouts packaged).decision 1 blockBit ∧
    (experiment.readouts rewritten).decision 0 = (experiment.readouts packaged).decision 0 :=
  ⟨blockBit_hidden, blockBit_available, rfl⟩

theorem terminal_quotient_fibers (x y : Cell) :
    (packaged.profile.grades 1).ofDual.r x y ↔ blockBit x = blockBit y :=
  Iff.rfl

theorem terminal_quotient_onto : Function.Surjective blockBit := by
  intro b
  cases b
  · exact ⟨2,rfl⟩
  · exact ⟨0,rfl⟩

theorem terminal_quotient_identifies : ∃ x y : Cell, x ≠ y ∧ blockBit x = blockBit y :=
  ⟨0,1,by decide,rfl⟩

def deletedProposal : Proposal Mark Bool Cell := (2,false,false,0,1)

theorem deleted_proposal_readout :
    (experiment.readouts initial).occurs deletedProposal ∧
      ¬ (experiment.readouts gated).occurs deletedProposal := by
  change deletedProposal ∈ (experiment.readouts initial).support ∧
    deletedProposal ∉ (experiment.readouts gated).support
  rw [experiment.readouts_support, experiment.readouts_support]
  change 0 < table false 2 false false 0 1 ∧ ¬ 0 < table true 2 false false 0 1
  norm_num [table, localGate]

/-- This is the full candidate domain of the post-gate packaging map. -/
abbrev RetainedProposal :=
  {p : Proposal Mark Bool Cell // (experiment.readouts gated).occurs p}

def proposalDestination (p : RetainedProposal) : Bool × Cell :=
  (p.val.2.2.1, p.val.2.2.2.2)

def asksForDeleted (p : Proposal Mark Bool Cell) : Prop := p = deletedProposal

theorem gate_candidate_nonempty : Nonempty RetainedProposal := by
  let p : Proposal Mark Bool Cell := (2,false,false,0,0)
  refine ⟨⟨p, ?_⟩⟩
  change p ∈ (experiment.readouts gated).support
  rw [experiment.readouts_support]
  change 0 < table true 2 false false 0 0
  norm_num [table, localGate]

theorem gate_unrealizable :
    (∀ p : RetainedProposal, ¬ asksForDeleted p.val) ∧
      asksForDeleted deletedProposal ∧ (experiment.readouts initial).occurs deletedProposal := by
  refine ⟨?_,rfl,deleted_proposal_readout.1⟩
  intro p h
  exact deleted_proposal_readout.2 (h ▸ p.property)

theorem license_cites_actual_routes :
    ¬ (experiment.readouts disclosed).licensed true ∧
      (experiment.readouts licensed).licensed true := by
  change true ∉ ({false} : Finset Bool) ∧ true ∈ ({false,true} : Finset Bool)
  decide

theorem publication_cites_actual_calibration :
    ¬ (experiment.readouts licensed).cited true ∧
      (experiment.readouts published).cited true := by
  change true ∉ ({false} : Finset Bool) ∧ true ∈ ({false,true} : Finset Bool)
  decide

theorem published_calibration_measured (x : Bool × Cell) :
    observedSignal parity (experiment.readouts published).trial 2 x () = 1/32 := by
  have h := experiment.published_calibration published (e := true)
    (show true ∈ published.profile.published from by decide)
    (show experiment.audit true = .calibration (2 : Mark) () (1/8) from rfl) x
  change observedSignal parity (experiment.readouts published).trial 2 x () = (1/4 : ℚ) * (1/8) at h
  norm_num at h
  exact h

end MovingProjection.Example
