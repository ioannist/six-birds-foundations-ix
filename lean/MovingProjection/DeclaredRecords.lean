import SixBirds.FATCD
import MovingProjection.RoleCertificates

/-! The finite record declarations used by the six selected witness rows.
Carrier reference lists, graph domains, record uses, and formula fields are
explicit. Formula truth is checked separately from record formation. -/

namespace MovingProjection.Example.Manuscript

open SixBirds

noncomputable section

inductive ContentName
  | microCarrier | sourceEq | targetEq | tokenMap | descentCheck
  | retainedCarrier | destinationCarrier | proposalMap | macroPredicate | realization
  | routeCarrier | move (m : Mark) | pathLeft | pathRight | routeComparison
  | clock | clockOrder
  | quotientDomain | quotientImage | terminalEq | terminalMap | terminalCheck
  | sourceTable | calibrationQuery | evaluatorCarrier | evaluatorMap
  | evaluationEvent | evaluationTrace | replayCheck | conformanceCheck
  deriving DecidableEq, Fintype

inductive RawId
  | named (name : ContentName)
  | micro (x : MarkedState)
  | proposal (x : Proposal Mark Bool Cell)
  | destination (x : Bool × Cell)
  | routePoint (x : routeStates disclosed)
  | grade (x : Fin 2)
  | register (x : Cell)
  | block (x : Bool)
  | config (x : CalibrationConfig)
  deriving DecidableEq, Fintype

def rawContent : Finset RawId := Finset.univ

inductive MapUse | update | packaging | other deriving DecidableEq
inductive RelationUse | quotient | realization deriving DecidableEq

def rawKind : RawId → RawKind
  | .named n => match n with
    | .sourceEq | .targetEq | .realization | .terminalEq => .relation
    | .tokenMap | .proposalMap | .move _ | .terminalMap | .evaluatorMap => .map
    | .macroPredicate => .predicate
    | .pathLeft | .pathRight => .path
    | .routeComparison | .descentCheck => .comparison
    | .clock => .index
    | .clockOrder => .order
    | .terminalCheck | .replayCheck | .conformanceCheck => .check
    | .evaluationEvent => .event
    | .evaluationTrace => .trace
    | _ => .object
  | _ => .state

def mapUse : ContentName → Option MapUse
  | .tokenMap => some .update
  | .proposalMap | .terminalMap => some .packaging
  | .move _ | .evaluatorMap => some .other
  | _ => none

def relationUse : ContentName → Option RelationUse
  | .sourceEq | .targetEq | .terminalEq => some .quotient
  | .realization => some .realization
  | _ => none

def rawRefs : RawId → Finset RawId
  | .named n => match n with
    | .microCarrier => updateDomain.image RawId.micro
    | .sourceEq | .targetEq => {.named .microCarrier} ∪ updateDomain.image RawId.micro
    | .tokenMap => {.named .microCarrier}
    | .descentCheck => {.named .tokenMap,.named .sourceEq,.named .targetEq,.named .microCarrier}
    | .retainedCarrier => retained.image RawId.proposal
    | .destinationCarrier => Finset.univ.image RawId.destination
    | .proposalMap => {.named .retainedCarrier,.named .destinationCarrier}
    | .macroPredicate => {.proposal deletedProposal}
    | .realization => {.named .macroPredicate,.named .retainedCarrier,.proposal deletedProposal} ∪
        retained.image RawId.proposal
    | .routeCarrier => Finset.univ.image RawId.routePoint
    | .move _ => {.named .routeCarrier}
    | .pathLeft => (Finset.univ.image (RawId.routePoint ∘ leftPath)) ∪
        {.named (.move 2),.named (.move 0),.named .routeCarrier}
    | .pathRight => (Finset.univ.image (RawId.routePoint ∘ rightPath)) ∪
        {.named (.move 3),.named (.move 0),.named .routeCarrier}
    | .routeComparison => {.named .pathLeft,.named .pathRight,.named .routeCarrier} ∪
        moveNames.image (fun m => .named (.move m))
    | .clock => gradeCarrier.image RawId.grade
    | .clockOrder => {.named .clock} ∪ gradeCarrier.image RawId.grade
    | .quotientDomain => quotientDomain.image RawId.register
    | .quotientImage => quotientImage.image RawId.block
    | .terminalEq => {.named .quotientDomain} ∪ quotientDomain.image RawId.register
    | .terminalMap => {.named .quotientDomain,.named .quotientImage}
    | .terminalCheck => {.named .terminalEq,.named .terminalMap,.named .quotientDomain,
        .named .quotientImage,.register 0,.register 1}
    | .sourceTable => {.micro (0,false,0)}
    | .calibrationQuery => {.named .sourceTable}
    | .evaluatorCarrier => Finset.univ.image RawId.config
    | .evaluatorMap => {.named .evaluatorCarrier}
    | .evaluationEvent => {.named .sourceTable,.named .calibrationQuery}
    | .evaluationTrace => {.named .evaluationEvent,.config .loaded,.config .accepted}
    | .replayCheck => {.named .evaluationTrace,.named .evaluatorMap,.config .loaded,.config .accepted}
    | .conformanceCheck => {.named .evaluatorMap,.named .sourceTable,.named .calibrationQuery}
  | _ => ∅

theorem raw_reference_closure (r : RawId) : rawRefs r ⊆ rawContent := by
  intro x _
  exact Finset.mem_univ x

def roleRecords : Role → Finset RawId
  | .P1 => {.named .microCarrier,.named .sourceEq,.named .targetEq,.named .tokenMap,
      .named .descentCheck}
  | .P2 => {.named .retainedCarrier,.named .destinationCarrier,.named .proposalMap,
      .named .macroPredicate,.named .realization,.proposal deletedProposal}
  | .P3 => {.named .routeCarrier,.named .pathLeft,.named .pathRight,.named .routeComparison} ∪
      moveNames.image (fun m => .named (.move m))
  | .P4 => {.named .clock,.named .clockOrder}
  | .P5 => {.named .quotientDomain,.named .quotientImage,.named .terminalEq,.named .terminalMap,
      .named .terminalCheck,.register 0,.register 1}
  | .P6 => {.named .evaluationEvent,.named .evaluationTrace,.named .replayCheck,.named .evaluatorMap}

def roleCluster (r : Role) : Finset RawId := by
  classical
  exact rawContent.filter fun x => ∃ i ∈ roleRecords r,
    Relation.ReflTransGen (fun a b => b ∈ rawRefs a) i x

theorem role_cluster_contains_records (r : Role) : roleRecords r ⊆ roleCluster r := by
  classical
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,.refl⟩

theorem role_cluster_closed (r : Role) (x : RawId) (hx : x ∈ roleCluster r) :
    rawRefs x ⊆ roleCluster r := by
  classical
  obtain ⟨_,i,hi,hpath⟩ := Finset.mem_filter.mp hx
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,hpath.tail hy⟩

def quotientClasses {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : A → B) : Finset (Finset A) :=
  (Finset.univ.image fun b => Finset.univ.filter fun a => f a = b).filter Finset.Nonempty

theorem quotientClasses_nonempty {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (f : A → B) {s : Finset A} (h : s ∈ quotientClasses f) : s.Nonempty :=
  (Finset.mem_filter.mp h).2

theorem quotientClasses_equivalence {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (f : A → B) (x y : A) :
    (∃ s ∈ quotientClasses f, x ∈ s ∧ y ∈ s) ↔ f x = f y := by
  constructor
  · rintro ⟨s,hs,hx,hy⟩
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  · intro h
    let s := Finset.univ.filter fun a => f a = f x
    have hx : x ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ x,rfl⟩
    have hy : y ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ y,h.symm⟩
    exact ⟨s,Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨f x,Finset.mem_univ _,rfl⟩,⟨x,hx⟩⟩,hx,hy⟩

theorem quotientClasses_disjoint {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (f : A → B) (s t : Finset A) (hs : s ∈ quotientClasses f)
    (ht : t ∈ quotientClasses f) (hne : s ≠ t) : Disjoint s t := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hs).1
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
  exact hne (by rw [← (Finset.mem_filter.mp hx).2, ← (Finset.mem_filter.mp hy).2])

def sourceClasses : Finset (Finset MarkedState) := quotientClasses (fun s => s.2.1)
def targetClasses : Finset (Finset MarkedState) := quotientClasses (fun s => (s.1,s.2.1))
def terminalClasses : Finset (Finset Cell) := quotientClasses blockBit

def recordedRules : RawId → List (List Mark × List Mark)
  | .named .routeComparison => sourceRules
  | _ => []

theorem recorded_rules_exact (q : List Mark × List Mark) :
    (∃ r ∈ rawContent, q ∈ recordedRules r) ↔ q ∈ sourceRules := by
  constructor
  · rintro ⟨r,_,h⟩
    have empty (h : q ∈ ([] : List (List Mark × List Mark))) : False := by
      have H := List.not_mem_nil (a := q)
      exact H h
    cases r with
    | named name => cases name <;> first | exact h | exact (empty h).elim
    | _ => exact (empty h).elim
  · exact fun h => ⟨.named .routeComparison,Finset.mem_univ _,h⟩

structure ContentCertificate where
  check : ContentFormula
  result : Bool
  deriving DecidableEq

def ContentCertificate.correct (c : ContentCertificate) : Prop :=
  c.check.holds ↔ c.result = true

def evaluationRecords : List ContentCertificate :=
  ⟨.evaluation deletedProposal,true⟩ :: retained.toList.map (fun p => ⟨.evaluation p,false⟩)

theorem evaluation_records_correct :
    ∀ c ∈ evaluationRecords, ContentCertificate.correct c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hm
  · simp [ContentCertificate.correct,ContentFormula.holds,asksForDeleted]
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    simp only [ContentCertificate.correct,ContentFormula.holds,Bool.false_eq_true]
    exact ⟨no_realizer_correct p (Finset.mem_toList.mp hp),False.elim⟩

def contentChecks : ContentName → List ContentCertificate
  | .descentCheck => [⟨.descent,true⟩]
  | .realization => ⟨.unrealizable,true⟩ :: evaluationRecords
  | .routeComparison => [⟨.monoid,true⟩]
  | .clockOrder => [⟨.gradeOrder,true⟩]
  | .terminalCheck => [⟨.quotient,true⟩]
  | .replayCheck => [⟨.replay,true⟩]
  | .conformanceCheck => [⟨.conforms,true⟩]
  | _ => []

def witnessOwner : Role → ContentName
  | .P1 => .descentCheck
  | .P2 => .realization
  | .P3 => .routeComparison
  | .P4 => .clockOrder
  | .P5 => .terminalCheck
  | .P6 => .replayCheck

theorem content_checks_correct (n : ContentName) :
    ∀ c ∈ contentChecks n, ContentCertificate.correct c := by
  have replay : CalibrationReplay replayGraph := matches_newly_published_query.1
  intro c hc
  cases n <;> simp only [contentChecks,List.mem_singleton,List.not_mem_nil] at hc
  case realization =>
    rcases List.mem_cons.mp hc with rfl | he
    · exact ⟨fun _ => rfl,fun _ => no_realizer_correct⟩
    · exact evaluation_records_correct c he
  all_goals
    subst c
    refine ⟨fun _ => rfl,fun _ => ?_⟩
  all_goals
    first | exact descent_correct | exact monoid_correct | exact order_correct |
      exact quotient_correct | exact replay | exact fun _ => rfl

end
end MovingProjection.Example.Manuscript
