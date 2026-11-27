import MovingProjection.BooleanEvents
import MovingProjection.NativeCertificate
import MovingProjection.SingleAdditiveLicence
import MovingProjection.WidenedOneState

/-! The certified singleton criterion and exactly-one-licence NCL reduction
in one statement on audited instruments. ComplexityBoundary.md gives the
binary running-time bounds and the external hardness source. The one-state
Boolean reduction follows as a supporting result. -/

namespace MovingProjection.EventExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq X]
  [Nonempty M] [Nonempty X] [Nonempty R]

theorem singleton_criterion (D : NativeExperiments M I X R Γ Δ) (a b : D.protocol.State n) :
    (ofNative D).Factorable (liftNative D a) (liftNative D b) ↔ a.profile ≤ b.profile ∧
      D.protocol.signature a.profile a.law = D.protocol.signature a.profile b.law :=
  (factorable_ofNative_iff D a b).trans (D.exact_six_iff a b)

variable [DecidableEq Γ] [DecidableEq Δ]

theorem singleton_certificate (D : NativeExperiments M I X R Γ Δ)
    (a b : CoreCertificate.Presented D n) :
    ∃ left right : CoreCertificate.Witness a.rows, ∃ answer,
      CoreCertificate.nativeCheck a.rows a.table b.table a.law b.law left right = some answer ∧
        (answer = true ↔ (ofNative D).Factorable (liftNative D a.state) (liftNative D b.state)) := by
  obtain ⟨left, right, answer, h⟩ := CoreCertificate.nativeCheck_complete D a b
  exact ⟨left, right, answer, h, (CoreCertificate.nativeCheck_sound D a b h).trans
    (factorable_ofNative_iff D a.state b.state).symm⟩

omit [Fintype M] [Fintype I] [Fintype Γ] [Fintype Δ] [DecidableEq M] [DecidableEq X]
  [Nonempty M] [Nonempty X] [Nonempty R] [DecidableEq Γ] [DecidableEq Δ] in
theorem eq_ofNative_of_singletons (E : EventExperiments M I X R Γ Δ)
    (h : ∀ g, E.second g = none) : E = ofNative E.native := by
  cases E with
  | mk native second =>
    have hs : second = fun _ => none := funext h
    cases hs
    rfl

open SingleAdditiveLicence in
/-- Joint semantic form of the complexity boundary. The certificate and
the network reduction both use the actual measured edit relation. -/
theorem complexity_boundary :
    (∀ {M I X R Γ Δ : Type*} {n : ℕ}
        [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
        [DecidableEq M] [DecidableEq I] [DecidableEq X] [DecidableEq Γ] [DecidableEq Δ]
        [Nonempty M] [Nonempty X] [Nonempty R]
        (D : NativeExperiments M I X R Γ Δ),
      (∀ a b : D.protocol.State n,
        (ofNative D).Factorable (liftNative D a) (liftNative D b) ↔
          a.profile ≤ b.profile ∧
          D.protocol.signature a.profile a.law = D.protocol.signature a.profile b.law) ∧
      (∀ a b : CoreCertificate.Presented D n,
        (∃ left right : CoreCertificate.Witness a.rows, ∃ answer,
          CoreCertificate.nativeCheck a.rows a.table b.table a.law b.law left right = some answer) ∧
        (∀ (left right : CoreCertificate.Witness a.rows) (answer : Bool),
          CoreCertificate.nativeCheck a.rows a.table b.table a.law b.law left right = some answer →
          (answer = true ↔ (ofNative D).Factorable (liftNative D a.state) (liftNative D b.state))))) ∧
    (∀ {E V : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
        (N : ConstraintLogic.Network E V) (short : Bool),
      (∃! g, ((nclInstrument N short).second g).isSome = true) ∧
      (∀ g, ((nclInstrument N short).native.license g).left.length =
        if ((nclInstrument N short).second g).isSome then (if short then 1 else 2) else 3) ∧
      0 < tolerance E V (BinaryBase E) ∧
      ∀ {a b : E → Bool} (ha : N.Legal a) (hb : N.Legal b),
        let x := nclEndpoint N a ha short
        let y := nclEndpoint N b hb short
        x.val.profile = y.val.profile ∧ x.val.profile.licenses = Finset.univ ∧
        ((nclInstrument N short).Factorable x y ↔ N.Flips a b) ∧
        ((nclInstrument N short).Chain (tolerance E V (BinaryBase E)) x y ↔ N.Flips a b) ∧
        (a ≠ b → x ≠ y)) := by
  constructor
  · intro M I X R Γ Δ n _ _ _ _ _ _ _ _ _ _ _ _ _ _ D
    refine ⟨singleton_criterion D, fun a b => ⟨CoreCertificate.nativeCheck_complete D a b, ?_⟩⟩
    intro left right answer h
    exact (CoreCertificate.nativeCheck_sound D a b h).trans
      (factorable_ofNative_iff D a.state b.state).symm
  · intro E V _ _ _ _ N short
    refine ⟨ncl_exactly_one N, fun g => ncl_licence_duration N g, tolerance_pos, ?_⟩
    intro a b ha hb
    exact ⟨rfl, rfl, ncl_fine_iff N ha hb, ncl_chain_iff N ha hb, ncl_endpoints_distinct N ha hb⟩

end MovingProjection.EventExperiments

namespace MovingProjection.OneStateEvents.BooleanReduction

open ClauseReconfiguration

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def widenedEndpoint (f : Formula I) (a : I → Bool) (ha : Satisfies f a) :=
  fromFixed (endpoint f a ha)

theorem widened_endpoints_distinct (f : Formula I) {a b : I → Bool}
    (ha : Satisfies f a) (hb : Satisfies f b) (hne : a ≠ b) :
    widenedEndpoint f a ha ≠ widenedEndpoint f b hb :=
  fun h => endpoints_distinct f ha hb hne (fromFixed_injective h)

theorem widened_fine_iff_flips (f : Formula I) {a b : I → Bool}
    (hf : NoTautologies f) (ha : Satisfies f a) (hb : Satisfies f b) :
    (widened (compile f).tests (compile f).floor (compile f).floor_pos).Factorable
      (widenedEndpoint f a ha) (widenedEndpoint f b hb) ↔ FlipChain f a b := by
  refine Iff.trans ?_ (native_fine_iff_flips f hf ha hb)
  exact forall_congr' fun ε => imp_congr_right fun _ =>
    widened_chain_iff (endpoint f a ha) (endpoint f b hb)

theorem widened_chain_iff_flips_of_le (f : Formula I) {a b : I → Bool}
    (hf : NoTautologies f) (ha : Satisfies f a) (hb : Satisfies f b)
    {ε : ℚ} (hε : 0 < ε) (hle : ε ≤ 2 * (compile f).floor) :
    (widened (compile f).tests (compile f).floor (compile f).floor_pos).Chain ε
      (widenedEndpoint f a ha) (widenedEndpoint f b hb) ↔ FlipChain f a b :=
  (widened_chain_iff (endpoint f a ha) (endpoint f b hb)).trans
    (native_chain_iff_flips_of_le f hf ha hb hε hle)

end MovingProjection.OneStateEvents.BooleanReduction
