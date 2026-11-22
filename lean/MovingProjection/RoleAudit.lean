import MovingProjection.DeclaredRecords

/-! Positive witnesses and their audit dependency order for the finite
description compiled from the coupled experiment. -/

namespace MovingProjection.Example.Manuscript

open SixBirds
noncomputable section

inductive Formula
  | content (f : ContentFormula)
  | witness (r : Role) (cluster : Finset RawId)
  deriving DecidableEq

def Formula.roleFree : Formula → Prop
  | .content _ => True
  | .witness .. => False

structure SignedCertificate where
  formula : Formula
  result : Bool
  deriving DecidableEq

def SignedCertificate.fromContent (c : ContentCertificate) : SignedCertificate :=
  ⟨.content c.check,c.result⟩

def SignedCertificate.correct (v : Formula → Prop) (c : SignedCertificate) : Prop :=
  v c.formula ↔ c.result = true

def SignedCertificate.premise (v : Formula → Prop) (c : SignedCertificate) : Prop :=
  if c.result then v c.formula else ¬ v c.formula

inductive ClaimName
  | sourceConformance
  | replay
  | witness (r : Role)
  deriving DecidableEq

structure ClaimAnnotation where
  namedInputs : Finset RawId
  statement : Formula
  scope : Finset RawId
  hypotheses : List Formula
  witnessCluster : Option (Role × Finset RawId)

def claim : ClaimName → ClaimAnnotation
  | .sourceConformance =>
      let inputs := insert (.named .conformanceCheck) (rawRefs (.named .conformanceCheck))
      ⟨inputs,.content .conforms,inputs,[],none⟩
  | .replay =>
      let inputs := insert (.named .evaluationEvent)
        (insert (.named .replayCheck) (rawRefs (.named .replayCheck)))
      ⟨inputs,.content .replay,inputs,[],none⟩
  | .witness r =>
      let C := roleCluster r
      ⟨C,.witness r C,C,[],some (r,C)⟩

def required : ClaimName → List SignedCertificate
  | .sourceConformance => (contentChecks .conformanceCheck).map SignedCertificate.fromContent
  | .replay => (contentChecks .replayCheck).map SignedCertificate.fromContent
  | .witness r => ⟨.witness r (roleCluster r),true⟩ ::
      (contentChecks (witnessOwner r)).map SignedCertificate.fromContent

structure AuditAnnotation where
  refersTo : ClaimName
  inputs : Finset RawId
  certificates : List SignedCertificate
  conclusion : Formula
  uncertified : Finset RawId

def auditEntry (k : ClaimName) : AuditAnnotation :=
  ⟨k,(claim k).namedInputs,required k,(claim k).statement,∅⟩

def allAudits : List AuditAnnotation :=
  auditEntry .sourceConformance :: auditEntry .replay ::
    (primitiveRoles.map (auditEntry ∘ ClaimName.witness))

def AuditAnnotation.roleFree (a : AuditAnnotation) : Prop :=
  a.conclusion.roleFree ∧ ∀ c ∈ a.certificates, c.formula.roleFree

/-- An entitlement by inclusion of the identical signed premise also
establishes entailment on the smaller class of well-typed interpretations. -/
def AuditAnnotation.entails (a : AuditAnnotation) : Prop :=
  ∀ interpretation : Formula → Prop,
    (∀ c ∈ a.certificates, c.premise interpretation) → interpretation a.conclusion

def AuditAnnotation.honest (v : Formula → Prop) (a : AuditAnnotation) : Prop :=
  (claim a.refersTo).namedInputs ⊆ a.inputs ∧ a.inputs ⊆ rawContent ∧
  (∀ c ∈ a.certificates, c.correct v) ∧
  (∀ c ∈ required a.refersTo, c ∈ a.certificates) ∧
  a.conclusion = (claim a.refersTo).statement ∧
  a.entails ∧ (claim a.refersTo).hypotheses = [] ∧ a.uncertified = ∅

theorem auditEntry_honest {v : Formula → Prop} (k : ClaimName)
    (h : ∀ c ∈ required k, c.correct v) : (auditEntry k).honest v := by
  refine ⟨fun _ hr => hr,fun x _ => Finset.mem_univ x,h,fun _ hc => hc,rfl,?_,?_,rfl⟩
  · intro I hI
    have hd : ⟨(claim k).statement,true⟩ ∈ required k := by
      cases k
      all_goals exact List.mem_cons_self
    exact hI _ hd
  · cases k <;> rfl

def evaluateContent : Formula → Prop
  | .content f => f.holds
  | .witness .. => False

def Audit0 (a : AuditAnnotation) : Prop :=
  a ∈ allAudits ∧ a.roleFree ∧ a.honest evaluateContent

theorem role_audit_outside_Audit0 (r : Role) : ¬ Audit0 (auditEntry (.witness r)) :=
  fun h => h.2.1.1

theorem replay_in_Audit0 : Audit0 (auditEntry .replay) := by
  refine ⟨List.mem_cons_of_mem _ List.mem_cons_self,?_,?_⟩
  · constructor
    · trivial
    · intro c hc
      simp only [auditEntry,required,contentChecks,List.map_cons,List.map_nil,
        List.mem_singleton] at hc
      subst c
      trivial
  · apply auditEntry_honest
    intro c hc
    obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact content_checks_correct .replayCheck cert hcert

/-- The row data apart from the formula fields and the separate Audit₀ entry.
All carriers in these conditions are the declared finite carrier lists. -/
def WitnessStructure : Role → Prop
  | .P1 =>
      mapUse .tokenMap = some .update ∧ relationUse .sourceEq = some .quotient ∧
      relationUse .targetEq = some .quotient ∧
      (∀ x y, (∃ s ∈ sourceClasses, x ∈ s ∧ y ∈ s) ↔ rewriteSourceRelation.r x y) ∧
      (∀ x y, (∃ s ∈ targetClasses, x ∈ s ∧ y ∈ s) ↔ rewriteTargetRelation.r x y)
  | .P2 =>
      mapUse .proposalMap = some .packaging ∧ relationUse .realization = some .realization ∧
      rawKind (.named .macroPredicate) = .predicate ∧ retained.Nonempty ∧
      deletedProposal ∉ retained ∧
      (∀ p, p ∈ realizers ↔ p ∈ retained ∧ asksForDeleted p) ∧
      (∀ p ∈ retained, ⟨.evaluation p,false⟩ ∈ evaluationRecords) ∧
      ⟨.evaluation deletedProposal,true⟩ ∈ evaluationRecords
  | .P3 =>
      leftPath 0 = rightPath 0 ∧ leftPath 2 = rightPath 2 ∧
      leftPath 1 = routeMove disclosed 2 (leftPath 0) ∧
      leftPath 2 = routeMove disclosed 0 (leftPath 1) ∧
      rightPath 1 = routeMove disclosed 3 (rightPath 0) ∧
      rightPath 2 = routeMove disclosed 0 (rightPath 1) ∧
      ∀ q, (∃ r ∈ rawContent, q ∈ recordedRules r) ↔ q ∈ sourceRules
  | .P4 =>
      rawKind (.named .clock) = .index ∧ rawKind (.named .clockOrder) = .order
  | .P5 =>
      mapUse .terminalMap = some .packaging ∧ relationUse .terminalEq = some .quotient ∧
      (∀ x y, (∃ s ∈ terminalClasses, x ∈ s ∧ y ∈ s) ↔ quotientRelation.r x y)
  | .P6 =>
      rawKind (.named .evaluationEvent) = .event ∧ rawKind (.named .evaluationTrace) = .trace ∧
      rawKind (.named .replayCheck) = .check ∧ rawKind (.named .evaluatorMap) = .map ∧
      .named .evaluationEvent ∈ rawRefs (.named .evaluationTrace) ∧
      .named .evaluationTrace ∈ rawRefs (.named .replayCheck)

theorem witness_structure_verified (r : Role) : WitnessStructure r := by
  cases r
  · exact ⟨rfl,rfl,rfl,quotientClasses_equivalence _,quotientClasses_equivalence _⟩
  · refine ⟨rfl,rfl,rfl,retained_nonempty,deleted_outside_retained,realizers_correct,?_,List.mem_cons_self⟩
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,Finset.mem_toList.mpr hp,rfl⟩)
  · exact ⟨rfl,rfl,declared_paths_defined.1,declared_paths_defined.2.1,declared_paths_defined.2.2.1,
      declared_paths_defined.2.2.2,recorded_rules_exact⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl,quotientClasses_equivalence _⟩
  · exact ⟨rfl,rfl,rfl,rfl,Finset.mem_insert_self _ _,Finset.mem_insert_self _ _⟩

def Witness (r : Role) (C : Finset RawId) : Prop :=
  roleRecords r ⊆ C ∧ C ⊆ rawContent ∧ (∀ x ∈ C, rawRefs x ⊆ C) ∧ WitnessStructure r ∧
  (∀ c ∈ contentChecks (witnessOwner r), c.correct) ∧
  (r = .P6 → ∃ a, Audit0 a ∧ a.refersTo = .replay ∧
    .named .evaluationEvent ∈ a.inputs ∧ .named .evaluationTrace ∈ a.inputs ∧
    .named .replayCheck ∈ a.inputs ∧ a.conclusion = .content .replay)

theorem all_exact_witnesses (r : Role) : Witness r (roleCluster r) := by
  refine ⟨role_cluster_contains_records r,fun x _ => Finset.mem_univ x,role_cluster_closed r,
    witness_structure_verified r,
    content_checks_correct _,?_⟩
  intro _
  refine ⟨auditEntry .replay,replay_in_Audit0,rfl,?_,?_,?_,rfl⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

def evaluate : Formula → Prop
  | .content f => f.holds
  | .witness r C => Witness r C

theorem all_audits_honest (a : AuditAnnotation) (ha : a ∈ allAudits) : a.honest evaluate := by
  rcases List.mem_cons.mp ha with rfl | ha
  · apply auditEntry_honest
    intro c hc
    obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact content_checks_correct _ cert hcert
  rcases List.mem_cons.mp ha with rfl | ha
  · apply auditEntry_honest
    intro c hc
    obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact content_checks_correct _ cert hcert
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
  apply auditEntry_honest
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨fun _ => rfl,fun _ => all_exact_witnesses r⟩
  · obtain ⟨cert,hcert,rfl⟩ := List.mem_map.mp hc
    exact content_checks_correct _ cert hcert

end
end MovingProjection.Example.Manuscript
