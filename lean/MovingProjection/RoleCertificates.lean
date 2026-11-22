import SixBirds.Roles
import MovingProjection.TokenDescent
import MovingProjection.RouteWitness
import MovingProjection.CalibrationReplay

/-! Typed finite data and the exact verification conditions for the selected
witness alternatives of Foundations II, §2. -/

namespace MovingProjection.Example
namespace Manuscript

noncomputable section

open SixBirds

def effect : Role → Effect
  | .P1 => .rewrite
  | .P2 => .gate
  | .P3 => .route
  | .P4 => .earlier
  | .P5 => .terminal
  | .P6 => .publication

def role : Effect → Role
  | .rewrite => .P1
  | .gate => .P2
  | .route => .P3
  | .earlier => .P4
  | .terminal => .P5
  | .publication => .P6

def roleEquiv : Role ≃ Effect :=
  ⟨effect,role,fun a => by cases a <;> rfl,fun a => by cases a <;> rfl⟩

def updateToken : Token := (2,7,0)
def updateGraph : MarkedState → MarkedState := tokenUpdate true updateToken
def updateDomain : Finset MarkedState := Finset.univ

/-- The formula of row W₁(a). Both declared relations list the entire
carrier, and the total update has a value at each listed input. -/
def DescentCheck : Prop :=
  (∀ x ∈ updateDomain, ∀ y : MarkedState,
    rewriteSourceRelation.r x y → y ∈ updateDomain) ∧
  (∃ x ∈ updateDomain, ∃ y ∈ updateDomain, x ≠ y ∧ rewriteSourceRelation.r x y) ∧
  (∀ x ∈ updateDomain, ∀ y ∈ updateDomain,
    rewriteSourceRelation.r x y → rewriteTargetRelation.r (updateGraph x) (updateGraph y))

theorem descent_correct : DescentCheck := by
  obtain ⟨x,y,hne,hEq⟩ := token_source_class_nontrivial
  exact ⟨fun _ _ _ _ => Finset.mem_univ _, ⟨x,Finset.mem_univ _,y,Finset.mem_univ _,hne,hEq⟩,
    fun x _ y _ h => token_descends true updateToken x y h⟩

noncomputable def retained : Finset (Proposal Mark Bool Cell) := by
  classical
  exact Finset.univ.filter (experiment.readouts gated).occurs

theorem retained_iff (p : Proposal Mark Bool Cell) :
    p ∈ retained ↔ (experiment.readouts gated).occurs p := by
  classical
  simp [retained]

theorem retained_nonempty : retained.Nonempty := by
  obtain ⟨p⟩ := gate_candidate_nonempty
  exact ⟨p.val,(retained_iff p.val).mpr p.property⟩

def realizers : Finset (Proposal Mark Bool Cell) := ∅

theorem realizers_correct (p : Proposal Mark Bool Cell) :
    p ∈ realizers ↔ p ∈ retained ∧ asksForDeleted p := by
  simp only [realizers, Finset.notMem_empty, false_iff]
  rintro ⟨hp,hd⟩
  exact gate_unrealizable.1 ⟨p,(retained_iff p).mp hp⟩ hd

def NoRealizerCheck : Prop := ∀ p ∈ retained, ¬ asksForDeleted p

theorem no_realizer_correct : NoRealizerCheck :=
  fun p hp => gate_unrealizable.1 ⟨p,(retained_iff p).mp hp⟩

theorem deleted_outside_retained : deletedProposal ∉ retained :=
  fun h => deleted_proposal_readout.2 ((retained_iff _).mp h)

def declaredProposalPackage (p : retained) : Bool × Cell :=
  proposalDestination ⟨p.val,(retained_iff p.val).mp p.property⟩

def sourceWord : List Mark := (testPair true).left
def targetWord : List Mark := (testPair true).right
def routeStart := reachedBy disclosed []
def routeEnd := reachedBy disclosed [2,0]

def leftPath : Fin 3 → routeStates disclosed
  | 0 => routeStart
  | 1 => reachedBy disclosed [2]
  | 2 => routeEnd

def rightPath : Fin 3 → routeStates disclosed
  | 0 => routeStart
  | 1 => reachedBy disclosed [3]
  | 2 => routeEnd

theorem declared_paths_defined :
    leftPath 1 = routeMove disclosed 2 (leftPath 0) ∧
    leftPath 2 = routeMove disclosed 0 (leftPath 1) ∧
    rightPath 1 = routeMove disclosed 3 (rightPath 0) ∧
    rightPath 2 = routeMove disclosed 0 (rightPath 1) := by
  refine ⟨(routeMove_reachedBy disclosed 2 []).symm,(routeMove_reachedBy disclosed 0 [2]).symm,
    (routeMove_reachedBy disclosed 3 []).symm,?_⟩
  change routeEnd = routeMove disclosed 0 (reachedBy disclosed [3])
  calc
    _ = routeMove disclosed 0 (reachedBy disclosed [2]) :=
      (routeMove_reachedBy disclosed 0 [2]).symm
    _ = _ := by
      have h₂ : routeMove disclosed 2 routeStart = reachedBy disclosed [2] :=
        routeMove_reachedBy disclosed 2 []
      have h₃ : routeMove disclosed 3 routeStart = reachedBy disclosed [3] :=
        routeMove_reachedBy disclosed 3 []
      rw [← h₂, ← h₃]
      exact newly_licensed_routes_parallel

def monoidCarrier : Finset Bool := Finset.univ
def moveNames : Finset Mark := Finset.univ

/-- The monoid alternative W₃(a), with the two elements recorded by the
rational labels 0 and 1 and multiplication the Boolean disjunction table. -/
def MonoidCheck : Prop :=
  false ∈ monoidCarrier ∧
  (∀ x ∈ monoidCarrier, ∀ y ∈ monoidCarrier, (x || y) ∈ monoidCarrier) ∧
  (∀ x ∈ monoidCarrier, ∀ y ∈ monoidCarrier, ∀ z ∈ monoidCarrier,
    ((x || y) || z) = (x || (y || z))) ∧
  (∀ x ∈ monoidCarrier, (false || x) = x ∧ (x || false) = x) ∧
  (∀ m ∈ moveNames, routeSeparator [m] ∈ monoidCarrier) ∧
  (∀ q ∈ sourceRules, routeSeparator q.1 = routeSeparator q.2) ∧
  routeSeparator sourceWord ≠ routeSeparator targetWord ∧
  (∀ q ∈ sourceRules, (∀ m ∈ q.1, m ∈ moveNames) ∧ (∀ m ∈ q.2, m ∈ moveNames)) ∧
  (∀ m ∈ sourceWord, m ∈ moveNames) ∧ (∀ m ∈ targetWord, m ∈ moveNames)

theorem monoid_correct : MonoidCheck :=
  ⟨Finset.mem_univ _,fun _ _ _ _ => Finset.mem_univ _,
    fun x _ y _ z _ => routeSeparator_monoid_laws.2 x y z,
    fun x _ => routeSeparator_monoid_laws.1 x,fun _ _ => Finset.mem_univ _,
    routeSeparator_checks_all_rules,routeSeparator_distinguishes,
    fun _ _ => ⟨fun _ _ => Finset.mem_univ _,fun _ _ => Finset.mem_univ _⟩,
    fun _ _ => Finset.mem_univ _,fun _ _ => Finset.mem_univ _⟩

def bitDecisionGrades (s : State) : Finset (Fin 2) := by
  classical
  exact Finset.univ.filter fun j => (experiment.readouts s).decision j blockBit

theorem bitDecisionGrades_mem (s : State) (j : Fin 2) :
    j ∈ bitDecisionGrades s ↔ (experiment.readouts s).decision j blockBit := by
  classical
  simp [bitDecisionGrades]

def gradeCarrier : Finset (Fin 2) := bitDecisionGrades disclosed

def OrderCheckOn (grades : Finset (Fin 2)) : Prop :=
  (∀ i ∈ grades, ¬ i < i) ∧
  (∀ i ∈ grades, ∀ j ∈ grades, ∀ k ∈ grades, i < j → j < k → i < k) ∧
  ∃ i ∈ grades, ∃ j ∈ grades, i < j

def OrderCheck : Prop := OrderCheckOn gradeCarrier

theorem order_correct : OrderCheck := by
  refine ⟨fun _ _ => lt_irrefl _,fun _ _ _ _ _ _ => lt_trans,
    0,(bitDecisionGrades_mem disclosed 0).mpr earlier_disclosure_changes_timed_test.2.1,
    1,(bitDecisionGrades_mem disclosed 1).mpr blockBit_available,by decide⟩

theorem earlier_stage_certificate_fails_without_earlier_disclosure :
    ¬ OrderCheckOn (bitDecisionGrades packaged) := by
  have atTerminal (j : Fin 2) (hj : j ∈ bitDecisionGrades packaged) : j = 1 := by
    fin_cases j
    · exact (earlier_disclosure_changes_timed_test.1 ((bitDecisionGrades_mem _ _).mp hj)).elim
    · rfl
  intro h
  obtain ⟨i,hi,j,hj,hlt⟩ := h.2.2
  rw [atTerminal i hi,atTerminal j hj] at hlt
  exact (lt_irrefl _) hlt

def quotientDomain : Finset Cell := Finset.univ
def quotientImage : Finset Bool := Finset.univ
def quotientRelation := (packaged.profile.grades 1).ofDual

def QuotientCheck : Prop :=
  (∀ x ∈ quotientDomain, ∀ y ∈ quotientDomain, quotientRelation.r x y ↔ blockBit x = blockBit y) ∧
  (0 : Cell) ≠ 1 ∧ blockBit 0 = blockBit 1 ∧
  (∀ z ∈ quotientImage, ∃ x ∈ quotientDomain, blockBit x = z) ∧
  (∀ x : Cell, quotientRelation.r x x → x ∈ quotientDomain) ∧
  (∀ x ∈ quotientDomain, blockBit x ∈ quotientImage)

theorem quotient_correct : QuotientCheck := by
  refine ⟨fun x _ y _ => terminal_quotient_fibers x y, by decide,rfl,?_,
    fun _ _ => Finset.mem_univ _,fun _ _ => Finset.mem_univ _⟩
  intro b _
  obtain ⟨u,h⟩ := terminal_quotient_onto b
  exact ⟨u,Finset.mem_univ _,h⟩

def replayGraph : CalibrationConfig → CalibrationConfig :=
  calibrationStep (experiment.readouts licensed).trial

/-- Names for the closed formula fields of the concrete finite description.
The evaluation equations give their expansion over the named data. -/
inductive ContentFormula
  | descent
  | unrealizable
  | evaluation (p : Proposal Mark Bool Cell)
  | monoid
  | gradeOrder
  | quotient
  | replay
  | conforms
  deriving DecidableEq

def ContentFormula.holds : ContentFormula → Prop
  | .descent => DescentCheck
  | .unrealizable => NoRealizerCheck
  | .evaluation p => asksForDeleted p
  | .monoid => MonoidCheck
  | .gradeOrder => OrderCheck
  | .quotient => QuotientCheck
  | .replay => CalibrationReplay replayGraph
  | .conforms => ∀ a, replayGraph a = calibrationStep (experiment.readouts licensed).trial a

end
end Manuscript
end MovingProjection.Example
