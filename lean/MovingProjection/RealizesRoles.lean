import MovingProjection.RoleAudit
import MovingProjection.QueryTables

/-! The published role predicates on the common experiment, with their
audits, activation attachments, and observational omission tests. -/

namespace MovingProjection.Example.Manuscript

open SixBirds
noncomputable section

structure ProjectionAnnotations where
  thresholdTargets : Finset RawId
  threshold : Option ContentFormula
  schemaTargets : Finset RawId
  schema : Role
  collapseTargets : Finset RawId
  collapseCases : List String
  levelTargets : Finset RawId
  level : Level
  nonclaimTargets : Finset RawId
  nonclaims : List String

def collapseCase : Role → String
  | .P1 => "The declared update splits a source class."
  | .P2 => "The retained proposal carrier contains a requested proposal."
  | .P3 => "The recorded rules identify the compared words."
  | .P4 => "The declared grade relation lacks a strict ordered pair."
  | .P5 => "The terminal package fibers disagree with the declared equivalence."
  | .P6 => "The stated check fails to replay on the named source data."

def annotations (r : Role) : ProjectionAnnotations where
  thresholdTargets := roleCluster r
  threshold := none
  schemaTargets := roleCluster r
  schema := r
  collapseTargets := roleCluster r
  collapseCases := [collapseCase r]
  levelTargets := roleCluster r
  level := .verification
  nonclaimTargets := roleCluster r
  nonclaims := ["The claim concerns this audited experiment and its declared instruments."]

def recordLevel (_ : RawId) : Level := .verification

def allClaims : List ClaimName :=
  .sourceConformance :: .replay :: primitiveRoles.map ClaimName.witness

def snapshots : Fin 9 → State
  | 0 => initial
  | 1 => gated
  | 2 => throughZero
  | 3 => rewritten
  | 4 => packaged
  | 5 => disclosed
  | 6 => licensed
  | 7 => published
  | 8 => opposite

structure FiniteDescription where
  content : Finset RawId
  claims : List ClaimName
  audits : List AuditAnnotation
  attachments : List (Role × ProjectionAnnotations)
  observations : Fin 9 → QueryTables Mark Bool Cell Bool Bool 1

def description : FiniteDescription :=
  ⟨rawContent,allClaims,allAudits,primitiveRoles.map (fun r => (r,annotations r)),
    fun j => experiment.tables (snapshots j)⟩

theorem source_table_reads_calibration :
    calibrationStep (description.observations 6).readBack.trial = replayGraph := by
  change calibrationStep (experiment.tables licensed).readBack.trial = _
  rw [experiment.tables_readBack]
  rfl

theorem all_snapshot_queries (j : Fin 9) :
    (description.observations j).readBack = experiment.readouts (snapshots j) :=
  experiment.tables_readBack _

def ClosedDescription (d : FiniteDescription) : Prop :=
  (∀ r ∈ d.content, rawRefs r ⊆ d.content) ∧
  (∀ k ∈ d.claims, (claim k).namedInputs ⊆ d.content ∧ (claim k).scope ⊆ d.content) ∧
  (∀ a ∈ d.audits, a.refersTo ∈ d.claims ∧ a.inputs ⊆ d.content) ∧
  (∀ t ∈ d.attachments, t.2.thresholdTargets ⊆ d.content ∧
    t.2.schemaTargets ⊆ d.content ∧ t.2.collapseTargets ⊆ d.content ∧
    t.2.levelTargets ⊆ d.content ∧ t.2.nonclaimTargets ⊆ d.content)

theorem description_closed : ClosedDescription description := by
  have subset (s : Finset RawId) : s ⊆ rawContent := fun x _ => Finset.mem_univ x
  refine ⟨fun r _ => raw_reference_closure r,fun k _ => ⟨subset _,subset _⟩,?_,
    fun t _ => ⟨subset _,subset _,subset _,subset _,subset _⟩⟩
  intro a ha
  refine ⟨?_,subset _⟩
  rcases List.mem_cons.mp ha with rfl | h
  · exact List.mem_cons_self
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))

def AuditedDescription (d : FiniteDescription) : Prop :=
  (∀ a ∈ d.audits, a.honest evaluate) ∧
  ∀ k ∈ d.claims, ∃ a ∈ d.audits, a.refersTo = k ∧ a.conclusion = (claim k).statement

theorem description_audited : AuditedDescription description := by
  refine ⟨all_audits_honest,?_⟩
  intro k hk
  refine ⟨auditEntry k,?_,rfl,rfl⟩
  rcases List.mem_cons.mp hk with rfl | hk
  · exact List.mem_cons_self
  rcases List.mem_cons.mp hk with rfl | hk
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hk
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))

def ActiveProjection (r : Role) (C : Finset RawId) : Prop :=
  ClosedDescription description ∧ AuditedDescription description ∧ Witness r C ∧
  (∃ a ∈ description.audits, a.honest evaluate ∧
    a.refersTo ∈ description.claims ∧ (claim a.refersTo).witnessCluster = some (r,C) ∧
    a.conclusion = .witness r C) ∧
  ∃ p, (r,p) ∈ description.attachments ∧
    p.thresholdTargets = C ∧ p.schemaTargets = C ∧ p.schema = r ∧
    p.collapseTargets = C ∧ p.levelTargets = C ∧ p.nonclaimTargets = C ∧
    p.collapseCases ≠ [] ∧ p.nonclaims ≠ [] ∧
    (∀ x ∈ C, recordLevel x = p.level) ∧
    (∀ f, p.threshold = some f →
      ∃ a ∈ description.audits, ⟨.content f,true⟩ ∈ a.certificates)

theorem all_roles_active (r : Role) : ActiveProjection r (roleCluster r) := by
  have hr : r ∈ primitiveRoles := by cases r <;> decide
  have hc : ClaimName.witness r ∈ description.claims :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
  have ha : auditEntry (.witness r) ∈ description.audits :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩))
  refine ⟨description_closed,description_audited,all_exact_witnesses r,
    ⟨auditEntry (.witness r),ha,all_audits_honest _ ha,hc,rfl,rfl⟩,?_⟩
  refine ⟨annotations r,List.mem_map.mpr ⟨r,hr,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,
    List.cons_ne_nil _ _,List.cons_ne_nil _ _,fun _ _ => rfl,?_⟩
  intro f hf
  cases hf

/-- Each check is tied to a change of an actual native test in the same edit
used in the corresponding omission bound. -/
def ExperimentalChange : Role → Prop
  | .P1 => (experiment.readouts gated).projected ≠ (experiment.readouts rewritten).projected
  | .P2 => (experiment.readouts initial).occurs deletedProposal ∧
      ¬ (experiment.readouts gated).occurs deletedProposal
  | .P3 => ¬ (experiment.readouts disclosed).licensed true ∧
      (experiment.readouts licensed).licensed true
  | .P4 => ¬ (experiment.readouts packaged).decision 0 blockBit ∧
      (experiment.readouts disclosed).decision 0 blockBit ∧
      (experiment.readouts packaged).decision 1 = (experiment.readouts disclosed).decision 1 ∧
      ¬ OrderCheckOn (bitDecisionGrades packaged)
  | .P5 => ¬ (experiment.readouts rewritten).decision 1 blockBit ∧
      (experiment.readouts packaged).decision 1 blockBit ∧
      (experiment.readouts rewritten).decision 0 = (experiment.readouts packaged).decision 0
  | .P6 => ¬ (experiment.readouts licensed).cited true ∧
      (experiment.readouts published).cited true

theorem witnesses_distinguish_actual_edits (r : Role) : ExperimentalChange r := by
  cases r
  · intro h
    have hspec := (experiment.readouts_projected_iff gated rewritten).mp h |>.2
    have hm := congrFun hspec (2,())
    norm_num [gated,rewritten,law,spectrum] at hm
  · exact deleted_proposal_readout
  · exact license_cites_actual_routes
  · exact ⟨earlier_disclosure_changes_timed_test.1,earlier_disclosure_changes_timed_test.2.1,
      earlier_disclosure_changes_timed_test.2.2,earlier_stage_certificate_fails_without_earlier_disclosure⟩
  · exact terminal_packaging_changes_timed_test
  · exact publication_cites_actual_calibration

theorem role_realization (r : Role) :
    ActiveProjection r (roleCluster r) ∧ ExperimentalChange r ∧
      (∀ ε : ℚ, 0 < ε → experiment.TableChain ε
        (experiment.record (before (effect r))) (experiment.record (after (effect r)))) ∧
      (∀ ε : ℚ, ¬ experiment.TableOmitting (effect r) ε
        (experiment.record (before (effect r))) (experiment.record (after (effect r)))) := by
  refine ⟨all_roles_active r,witnesses_distinguish_actual_edits r,
    (experiment.table_factorization_iff _ _).mpr (adjacent_factorable (effect r)),?_⟩
  exact fun ε h => omission_fails (effect r) ε ((experiment.table_omitting_iff _ _ _ _).mp h)

theorem one_recorded_edit_needs_all_six :
    (∀ ε : ℚ, 0 < ε → experiment.TableChain ε
      (experiment.record initial) (experiment.record published)) ∧
    ∀ (r : Role) (ε : ℚ), ¬ experiment.TableOmitting (effect r) ε
      (experiment.record initial) (experiment.record published) :=
  ⟨(experiment.table_factorization_iff _ _).mpr single_edit_requires_all_six.1,
    fun r ε h => single_edit_requires_all_six.2 (effect r) ε
      ((experiment.table_omitting_iff _ _ _ _).mp h)⟩

theorem recorded_obstruction :
    ¬ experiment.TableChain obstructionTolerance
      (experiment.record initial) (experiment.record opposite) :=
  fun h => obstruction_at_native_tolerance ((experiment.table_chain_iff _ _ _).mp h)

theorem every_effect_occurs (r : Role) (ε : ℚ) (hε : 0 < ε) :
    ∃ a b : State, a ≠ b ∧
      NativeReadouts.typedEdit (experiment.attained 1) ε (effect r)
        (experiment.readouts a) (experiment.readouts b) := by
  classical
  by_contra h
  have deleteIdentity {a b : State} (hc : D.Chain ε a b) :
      D.Omitting (effect r) ε a b := by
    induction hc with
    | refl => exact .refl
    | @tail x y hz hs ih =>
      obtain ⟨k,hk⟩ := hs
      by_cases hr : k = effect r
      · subst k
        by_cases he : x = y
        · simpa only [he] using ih
        · exact (h ⟨x,y,he,(experiment.typed_edit_iff_step _ _ _ _).mpr hk⟩).elim
      · exact ih.tail ⟨k,hr,hk⟩
  exact omission_fails (effect r) ε
    (deleteIdentity (adjacent_factorable (effect r) ε hε))

end
end MovingProjection.Example.Manuscript
