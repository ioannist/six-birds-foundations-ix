import MovingProjection.Classification
import Mathlib.Order.Closure
import Mathlib.Data.Finset.Powerset

/-! Order properties of the least reduct, with no inhabitation hypothesis. -/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem core_subset (rows : List (ExponentRow I)) (s : Finset I) : core rows s ⊆ s :=
  (isCore_core rows s).1.subset

theorem core_idempotent (rows : List (ExponentRow I)) (s : Finset I) :
    core rows (core rows s) = core rows s :=
  (core_eq_of_reduces (isCore_core rows s).1).symm

theorem core_mono_support (rows : List (ExponentRow I)) :
    Monotone (core rows) := by
  intro s t hst
  have h := (isCore_core rows t).1.restrict hst
  exact ((isCore_core rows s).2 _ h).trans Finset.inter_subset_right

omit [DecidableEq I] in
theorem Contracts.of_rows_subset {rows more : List (ExponentRow I)}
    (h : rows ⊆ more) {s t : Finset I} (hc : Contracts more s t) : Contracts rows s t := by
  obtain ⟨w,hw,he⟩ := hc
  exact ⟨w, ⟨hw.1, fun r hr => hw.2 r (h hr)⟩, he⟩

omit [DecidableEq I] in
theorem Reduces.of_rows_subset {rows more : List (ExponentRow I)}
    (h : rows ⊆ more) {s t : Finset I} (hr : Reduces more s t) : Reduces rows s t :=
  hr.mono (fun _ _ hc => Contracts.of_rows_subset h hc)

theorem core_mono_rows {rows more : List (ExponentRow I)} (h : rows ⊆ more) (s : Finset I) :
    core rows s ⊆ core more s :=
  (isCore_core rows s).2 _ (Reduces.of_rows_subset h (isCore_core more s).1)

theorem core_absorb_rows {rows more : List (ExponentRow I)} (h : rows ⊆ more) (s : Finset I) :
    core rows (core more s) = core rows s ∧ core more (core rows s) = core rows s := by
  refine ⟨(core_eq_of_reduces (Reduces.of_rows_subset h (isCore_core more s).1)).symm, ?_⟩
  apply Finset.Subset.antisymm (core_subset _ _)
  simpa only [core_idempotent] using core_mono_rows h (core rows s)

theorem codeSupport_signedCore (rows : List (ExponentRow I)) (s : I → SignType) :
    codeSupport (signedCore rows s) = core rows (codeSupport s) := by
  ext i
  have mem (t : I → SignType) : i ∈ codeSupport t ↔ t i ≠ 0 := by simp [codeSupport]
  rw [mem]
  by_cases hi : i ∈ core rows (codeSupport s)
  · have hs := (mem s).mp (core_subset rows (codeSupport s) hi)
    simp [signedCore, hi, hs]
  · simp [signedCore, hi]

theorem signedCore_absorb_rows {rows more : List (ExponentRow I)} (h : rows ⊆ more)
    (s : I → SignType) :
    signedCore rows (signedCore more s) = signedCore rows s ∧
    signedCore more (signedCore rows s) = signedCore rows s := by
  have hsupports := core_absorb_rows h (codeSupport s)
  constructor <;> funext i
  · change (if i ∈ core rows (codeSupport (signedCore more s)) then
        signedCore more s i else 0) = signedCore rows s i
    rw [codeSupport_signedCore, hsupports.1]
    by_cases hi : i ∈ core rows (codeSupport s)
    · have hj := core_mono_rows h (codeSupport s) hi
      simp [signedCore, hi, hj]
    · simp [signedCore, hi]
  · change (if i ∈ core more (codeSupport (signedCore rows s)) then
        signedCore rows s i else 0) = signedCore rows s i
    rw [codeSupport_signedCore, hsupports.2]
    by_cases hi : i ∈ core rows (codeSupport s) <;> simp [signedCore, hi]

theorem signedCore_eq_of_rows_subset {rows more : List (ExponentRow I)} (h : rows ⊆ more)
    {s t : I → SignType} (he : signedCore more s = signedCore more t) :
    signedCore rows s = signedCore rows t :=
  ((signedCore_absorb_rows h s).1.symm.trans (congrArg (signedCore rows) he)).trans
    (signedCore_absorb_rows h t).1

omit [DecidableEq I] in
theorem FineConnected.of_tests_subset {tests more : List (MonomialTest I)}
    {budgets : List (MarkBudget I)} {x y : I → ℚ}
    (h : tests ⊆ more) (hf : FineConnected more budgets x y) :
    FineConnected tests budgets x y := by
  have forget {v : I → ℚ} (hv : Legal more budgets v) : Legal tests budgets v :=
    ⟨fun t ht => hv.1 t (h ht),hv.2⟩
  intro ε hε
  exact (hf ε hε).mono (fun _ _ step => ⟨forget step.1, forget step.2.1,step.2.2⟩)

/-- No proper contraction is available. This is equivalent to admitting no
proper reduct, because every reduction is a chain of contractions. -/
def IrreducibleSupport (rows : List (ExponentRow I)) (s : Finset I) : Prop :=
  ∀ t, Contracts rows s t → t = s

theorem irreducibleSupport_iff_core_eq (rows : List (ExponentRow I)) (s : Finset I) :
    IrreducibleSupport rows s ↔ core rows s = s := by
  constructor
  · intro h
    have hh : ∀ t, Reduces rows s t → t = s := by
      intro t ht
      induction ht with
      | refl => rfl
      | tail _ hc ih => subst ih; exact h _ hc
    exact hh _ (isCore_core rows s).1
  · intro h t ht
    exact Finset.Subset.antisymm ht.subset (h ▸ (isCore_core rows s).2 t (.single ht))

theorem core_eq_self_of_damping_zero {rows : List (ExponentRow I)} {s : Finset I}
    (h : ∀ w, Damping rows s w → ∀ i ∈ s, w i = 0) :
    core rows s = s := by
  apply (irreducibleSupport_iff_core_eq rows s).1
  rintro t ⟨w,hw,rfl⟩
  exact Finset.filter_true_of_mem (h w hw)

theorem IrreducibleSupport.subset_core {rows : List (ExponentRow I)} {u s : Finset I}
    (hir : IrreducibleSupport rows u) (hsub : u ⊆ s) : u ⊆ core rows s :=
  ((irreducibleSupport_iff_core_eq rows u).1 hir) ▸ core_mono_support rows hsub

theorem core_greatest_irreducible (rows : List (ExponentRow I)) (s : Finset I) :
    IsGreatest {u | u ⊆ s ∧ IrreducibleSupport rows u} (core rows s) := by
  refine ⟨⟨core_subset _ _, (irreducibleSupport_iff_core_eq _ _).2 (core_idempotent _ _)⟩, ?_⟩
  intro u hu
  exact IrreducibleSupport.subset_core hu.2 hu.1

theorem core_eq_union_irreducible (rows : List (ExponentRow I)) (s : Finset I) :
    core rows s = (by classical exact (s.powerset.filter (IrreducibleSupport rows)).biUnion id) := by
  classical
  ext i
  have h := core_greatest_irreducible rows s
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset, id_eq]
  exact ⟨fun hi => ⟨_,h.1,hi⟩, fun ⟨_,hu,hi⟩ => hu.2.subset_core hu.1 hi⟩

theorem core_eq_empty_iff (rows : List (ExponentRow I)) (s : Finset I) :
    core rows s = ∅ ↔ ∀ u ⊆ s, IrreducibleSupport rows u → u = ∅ := by
  have h := core_greatest_irreducible rows s
  constructor
  · intro he u hu hir
    have hsub : u ⊆ core rows s := hir.subset_core hu
    rw [he] at hsub
    exact Finset.subset_empty.mp hsub
  · intro he
    exact he _ h.1.1 h.1.2

theorem core_eq_empty_of_positive_damping {rows : List (ExponentRow I)} {s : Finset I}
    {w : I → ℕ} (hw : Damping rows s w) (hpos : ∀ i ∈ s, 0 < w i) :
    core rows s = ∅ := by
  have he : s.filter (fun i => w i = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    exact fun i hi => (hpos i hi).ne'
  exact Finset.subset_empty.mp ((isCore_core rows s).2 _ (.single ⟨w,hw,he.symm⟩))

/-- An active row of equal total degrees admits uniform damping on the support. -/
theorem core_eq_empty_of_balanced_active {rows : List (ExponentRow I)} {s : Finset I}
    (h : ∀ r ∈ rows, r.active s → ∑ i, r.lhs i = ∑ i, r.rhs i) : core rows s = ∅ := by
  let w (i : I) := if i ∈ s then 1 else 0
  apply core_eq_empty_of_positive_damping (w := w)
  · refine ⟨fun i hi => by simp [w, hi], fun r hr ha => ?_⟩
    have weight (f : I → ℕ) (hf : ∀ i ∉ s, f i = 0) :
        ∑ i, f i * w i = ∑ i, f i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [w, hi]
      · simp [w, hi, hf i hi]
    rw [weight _ (fun i hi => (ha i hi).1), weight _ (fun i hi => (ha i hi).2)]
    exact h r hr ha
  · intro i hi
    simp [w, hi]

theorem fineConnected_of_empty_cores {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y : I → ℚ} (hx : Legal tests budgets x) (hy : Legal tests budgets y)
    (hcx : core (tests.map MonomialTest.row) (support x) = ∅)
    (hcy : core (tests.map MonomialTest.row) (support y) = ∅) :
    FineConnected tests budgets x y := by
  have toZero {v : I → ℚ} (hv : Legal tests budgets v)
      (hc : core (tests.map MonomialTest.row) (support v) = ∅) :
      FineConnected tests budgets v 0 := by
    obtain ⟨u,_,hf,hs,_⟩ := fineConnected_to_core hv
    have he : u = 0 := by
      funext i
      by_contra hn
      have hi := mem_support.mpr (show u i ≠ 0 from hn)
      simp [hs, hc] at hi
    exact he ▸ hf
  exact (toZero hx hcx).trans (toZero hy hcy).symm

/-- On supports the core is an interior operator, or equivalently a closure
operator in the reverse-inclusion order. -/
noncomputable def coreInterior (rows : List (ExponentRow I)) :
    ClosureOperator (Finset I)ᵒᵈ where
  toFun s := OrderDual.toDual (core rows s.ofDual)
  monotone' := fun _ _ h => core_mono_support rows h
  le_closure' s := core_subset rows s.ofDual
  idempotent' s := core_idempotent rows s.ofDual

/-- On subsets of a fixed finite universe, close the set of removed coordinates. -/
noncomputable def removedClosure (rows : List (ExponentRow I)) (J : Finset I) :
    ClosureOperator (Set.Iic J) where
  toFun z := ⟨J \ core rows (J \ z.val), Finset.sdiff_subset⟩
  monotone' _ _ h :=
    Finset.sdiff_subset_sdiff (by rfl) (core_mono_support rows
      (Finset.sdiff_subset_sdiff (by rfl) h))
  le_closure' z := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨z.property hi, fun hc =>
      (Finset.mem_sdiff.mp (core_subset _ _ hc)).2 hi⟩
  idempotent' z := by
    apply Subtype.ext
    change J \ core rows (J \ (J \ core rows (J \ z.val))) =
      J \ core rows (J \ z.val)
    rw [Finset.sdiff_sdiff_eq_self ((core_subset rows _).trans Finset.sdiff_subset), core_idempotent]

theorem removedClosure_isClosed_iff (rows : List (ExponentRow I)) (J : Finset I)
    (z : Set.Iic J) :
    (removedClosure rows J).IsClosed z ↔ IrreducibleSupport rows (J \ z.val) := by
  rw [(removedClosure rows J).isClosed_iff, irreducibleSupport_iff_core_eq]
  change (⟨J \ core rows (J \ z.val), Finset.sdiff_subset⟩ : Set.Iic J) = z ↔ _
  constructor
  · intro h
    have hh := congrArg (fun z : Set.Iic J => J \ z.val) h
    change J \ (J \ core rows (J \ z.val)) = J \ z.val at hh
    rwa [Finset.sdiff_sdiff_eq_self ((core_subset rows _).trans Finset.sdiff_subset)] at hh
  · intro h
    apply Subtype.ext
    change J \ core rows (J \ z.val) = z.val
    rw [h, Finset.sdiff_sdiff_eq_self z.property]

end MovingProjection
