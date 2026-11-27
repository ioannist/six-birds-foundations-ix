import MovingProjection.Classification
import MovingProjection.Experiments

/-! Executable proof checking for signed support reductions. The search for a
certificate is independent of the checker. -/

namespace MovingProjection
namespace CoreCertificate

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def activeCheck (row : ExponentRow I) (s : Finset I) : Bool :=
  decide (∀ i, i ∉ s → row.lhs i = 0 ∧ row.rhs i = 0)

@[simp] theorem activeCheck_eq_true {row : ExponentRow I} {s : Finset I} :
    activeCheck row s = true ↔ row.active s := by
  simp [activeCheck, ExponentRow.active]

def dampingCheck (rows : List (ExponentRow I)) (s : Finset I) (w : I → ℕ) : Bool :=
  decide (∀ i, i ∉ s → w i = 0) && rows.all fun row =>
    !activeCheck row s || decide ((∑ i, row.lhs i * w i) = ∑ i, row.rhs i * w i)

@[simp] theorem dampingCheck_eq_true {rows : List (ExponentRow I)} {s : Finset I}
    {w : I → ℕ} : dampingCheck rows s w = true ↔ Damping rows s w := by
  simp only [dampingCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.eq_false_iff,
    Damping]
  simp only [ne_eq, activeCheck_eq_true, or_iff_not_imp_left, not_not]

def replay (rows : List (ExponentRow I)) (s : Finset I) : List (I → ℕ) → Option (Finset I)
  | [] => some s
  | w :: rest =>
    if dampingCheck rows s w then replay rows (s.filter fun i => w i = 0) rest else none

theorem replay_sound {rows : List (ExponentRow I)} {s t : Finset I} {steps : List (I → ℕ)}
    (h : replay rows s steps = some t) : Reduces rows s t := by
  induction steps generalizing s with
  | nil => simp [replay] at h; subst t; exact .refl
  | cons w rest ih =>
    by_cases hw : dampingCheck rows s w = true
    · simp [replay, hw] at h
      exact Relation.ReflTransGen.head ⟨w, dampingCheck_eq_true.mp hw, rfl⟩ (ih h)
    · simp [replay, hw] at h

theorem replay_complete {rows : List (ExponentRow I)} {s t : Finset I}
    (h : Reduces rows s t) : ∃ steps, replay rows s steps = some t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl⟩
  | head hstep _ ih =>
    obtain ⟨w, hw, rfl⟩ := hstep
    obtain ⟨steps, hs⟩ := ih
    exact ⟨w :: steps, by simpa [replay, dampingCheck_eq_true.mpr hw] using hs⟩

theorem replay_complete_short {rows : List (ExponentRow I)} {s t : Finset I}
    (h : Reduces rows s t) :
    ∃ steps, replay rows s steps = some t ∧ steps.length + t.card ≤ s.card := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], rfl, by simp⟩
  | @head s u hstep _ ih =>
    obtain ⟨steps, hs, hsize⟩ := ih
    by_cases he : s = u
    · subst u
      exact ⟨steps, hs, hsize⟩
    · have hstrict : u.card < s.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hstep.subset, Ne.symm he⟩)
      obtain ⟨w, hw, rfl⟩ := hstep
      exact ⟨w :: steps, by simpa [replay, dampingCheck_eq_true.mpr hw] using hs, by
        simp only [List.length_cons]
        omega⟩

/-- Inactive rows contribute zero. An integer multiplier vector may be stored sparsely. -/
def dualCoordinate (rows : List (ExponentRow I)) (s : Finset I)
    (multipliers : Fin rows.length → ℤ) (i : I) : ℤ :=
  ∑ k, if activeCheck rows[k] s then
    multipliers k * ((rows[k].lhs i : ℤ) - (rows[k].rhs i : ℤ)) else 0

def terminalCheck (rows : List (ExponentRow I)) (s : Finset I)
    (multipliers : Fin rows.length → ℤ) : Bool :=
  decide (∀ i ∈ s, 0 < dualCoordinate rows s multipliers i)

theorem dual_dot_zero {rows : List (ExponentRow I)} {s : Finset I} {w : I → ℕ}
    (hw : Damping rows s w) (multipliers : Fin rows.length → ℤ) :
    ∑ i, dualCoordinate rows s multipliers i * (w i : ℤ) = 0 := by
  simp only [dualCoordinate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : activeCheck rows[k] s = true
  · simp only [hk, if_true, mul_assoc]
    rw [← Finset.mul_sum, show (∑ i, ((rows[k].lhs i : ℤ) - (rows[k].rhs i : ℤ)) * (w i : ℤ)) = 0 by
      simp only [sub_mul, Finset.sum_sub_distrib]
      have hh := hw.2 rows[k] (List.getElem_mem k.isLt) (activeCheck_eq_true.mp hk)
      exact sub_eq_zero.mpr (by exact_mod_cast hh), mul_zero]
  · simp only [if_neg hk, zero_mul, Finset.sum_const_zero]

theorem terminalCheck_sound {rows : List (ExponentRow I)} {s t : Finset I}
    {multipliers : Fin rows.length → ℤ} (h : terminalCheck rows s multipliers = true)
    (hst : Contracts rows s t) : t = s := by
  have hpos : ∀ i ∈ s, 0 < dualCoordinate rows s multipliers i := of_decide_eq_true h
  obtain ⟨w, hw, rfl⟩ := hst
  apply Finset.filter_eq_self.mpr
  intro i hi
  have hnonneg : ∀ j ∈ (Finset.univ : Finset I),
      0 ≤ dualCoordinate rows s multipliers j * (w j : ℤ) := by
    intro j _
    by_cases hj : j ∈ s
    · exact mul_nonneg (hpos j hj).le (Int.natCast_nonneg _)
    · simp [hw.1 j hj]
  have hi' := Finset.single_le_sum hnonneg (Finset.mem_univ i)
  rw [dual_dot_zero hw] at hi'
  have hw' : ¬ 0 < (w i : ℤ) := fun hp =>
    (not_lt_of_ge hi') (mul_pos (hpos i hi) hp)
  omega

theorem replay_terminal_isCore {rows : List (ExponentRow I)} {s t : Finset I}
    {steps : List (I → ℕ)} {multipliers : Fin rows.length → ℤ}
    (hr : replay rows s steps = some t) (ht : terminalCheck rows t multipliers = true) :
    IsCore rows s t := by
  have hst := replay_sound hr
  have heq : core rows t = t := by
    have hfixed : ∀ u, Reduces rows t u → u = t := by
      intro u hu
      induction hu with
      | refl => rfl
      | @tail v u _ hstep ih =>
        subst v
        exact terminalCheck_sound ht hstep
    exact hfixed _ (isCore_core rows t).1
  have hc := core_eq_of_reduces hst
  rw [heq] at hc
  exact hc ▸ isCore_core rows s

structure Witness (rows : List (ExponentRow I)) where
  steps : List (I → ℕ)
  terminal : Fin rows.length → ℤ

def checkCore (rows : List (ExponentRow I)) (s : Finset I) (certificate : Witness rows) :
    Option (Finset I) := do
  let t ← replay rows s certificate.steps
  if terminalCheck rows t certificate.terminal then some t else none

theorem checkCore_sound {rows : List (ExponentRow I)} {s t : Finset I}
    {certificate : Witness rows} (h : checkCore rows s certificate = some t) :
    IsCore rows s t := by
  cases hr : replay rows s certificate.steps with
  | none => simp [checkCore, hr] at h
  | some u =>
    by_cases ht : terminalCheck rows u certificate.terminal = true
    · have heq : u = t := by simpa [checkCore, hr, ht] using h
      subst u
      exact replay_terminal_isCore hr ht
    · simp [checkCore, hr, ht] at h

def checkPair (rows : List (ExponentRow I)) (x y : I → ℚ)
    (left right : Witness rows) : Option Bool :=
  match checkCore rows (support x) left, checkCore rows (support y) right with
  | some c, some d => some (decide (c = d ∧ ∀ i : I, i ∈ c → (0 < x i ↔ 0 < y i)))
  | _, _ => none

theorem signedCore_eq_iff {rows : List (ExponentRow I)} {x y : I → ℚ} {c d : Finset I}
    (hc : IsCore rows (support x) c) (hd : IsCore rows (support y) d) :
    signedCore rows (signCode (embed x)) = signedCore rows (signCode (embed y)) ↔
      c = d ∧ ∀ i : I, i ∈ c → (0 < x i ↔ 0 < y i) := by
  have hx : codeSupport (signCode (embed x)) = support x :=
    (codeSupport_signCode _).trans (realSupport_cast x)
  have hy : codeSupport (signCode (embed y)) = support y :=
    (codeSupport_signCode _).trans (realSupport_cast y)
  have hcx := (isCore_core rows (support x)).unique hc
  have hdy := (isCore_core rows (support y)).unique hd
  have hsign (i : I) (hi : i ∈ support x) (hj : i ∈ support y) :
      signCode (embed x) i = signCode (embed y) i ↔ (0 < x i ↔ 0 < y i) := by
    have xi : x i ≠ 0 := mem_support.mp hi
    have yi : y i ≠ 0 := mem_support.mp hj
    rcases lt_or_gt_of_ne xi with hx' | hx' <;> rcases lt_or_gt_of_ne yi with hy' | hy'
    all_goals
      have hxr : (x i : ℝ) < 0 ∨ 0 < (x i : ℝ) := by exact_mod_cast (lt_or_gt_of_ne xi)
      have hyr : (y i : ℝ) < 0 ∨ 0 < (y i : ℝ) := by exact_mod_cast (lt_or_gt_of_ne yi)
      rcases hxr with hxr | hxr <;> rcases hyr with hyr | hyr <;>
        simp_all [signCode, embed, sign_neg, sign_pos, not_lt_of_gt]
  have hnonzero (a : I → ℚ) (i : I) (hi : i ∈ support a) : signCode (embed a) i ≠ 0 := by
    have he := (codeSupport_signCode (embed a)).trans (realSupport_cast a)
    have h : i ∈ codeSupport (signCode (embed a)) := by
      rwa [he]
    exact (Finset.mem_filter.mp h).2
  unfold signedCore
  rw [hx, hy, hcx, hdy]
  constructor
  · intro h
    have hcd : c = d := by
      ext i
      have hi := congrFun h i
      by_cases hci : i ∈ c <;> by_cases hdi : i ∈ d
      · simp [hci, hdi]
      · have hh := hnonzero x i (hc.1.subset hci)
        simp only [hci, hdi, if_true, if_false] at hi
        exact (hh hi).elim
      · have hh := hnonzero y i (hd.1.subset hdi)
        simp only [hci, hdi, if_true, if_false] at hi
        exact (hh hi.symm).elim
      · simp [hci, hdi]
    refine ⟨hcd, fun i hi => (hsign i (hc.1.subset hi) (hd.1.subset (hcd ▸ hi))).mp ?_⟩
    simpa [hi, ← hcd] using congrFun h i
  · rintro ⟨rfl, h⟩
    funext i
    by_cases hi : i ∈ c
    · simpa [hi] using (hsign i (hc.1.subset hi) (hd.1.subset hi)).mpr (h i hi)
    · simp [hi]

theorem checkPair_signature {rows : List (ExponentRow I)} {x y : I → ℚ}
    {left right : Witness rows} {answer : Bool}
    (h : checkPair rows x y left right = some answer) :
    (answer = true ↔ signedCore rows (signCode (embed x)) = signedCore rows (signCode (embed y))) := by
  cases hc : checkCore rows (support x) left with
  | none => simp [checkPair, hc] at h
  | some c =>
    cases hd : checkCore rows (support y) right with
    | none => simp [checkPair, hc, hd] at h
    | some d =>
      have heq : decide (c = d ∧ ∀ i : I, i ∈ c → (0 < x i ↔ 0 < y i)) = answer := by
        simpa [checkPair, hc, hd] using h
      rw [← heq, decide_eq_true_eq]
      exact (signedCore_eq_iff (checkCore_sound hc) (checkCore_sound hd)).symm

theorem checkPair_sound {tests : List (MonomialTest I)} {budgets : List (MarkBudget I)}
    {x y : I → ℚ} (hx : Legal tests budgets x) (hy : Legal tests budgets y)
    (hbound : ∃ B : ℝ, ∀ a, Legal tests budgets a → ‖embed a‖ ≤ B)
    {left right : Witness (tests.map MonomialTest.row)} {answer : Bool}
    (h : checkPair (tests.map MonomialTest.row) x y left right = some answer) :
    (answer = true ↔ FineConnected tests budgets x y) :=
  (checkPair_signature h).trans (fineConnected_iff_signedCore hx hy hbound).symm

section Native

variable {M X R Γ Δ : Type*} [Fintype M] [Fintype X] [Fintype R]
  [Fintype Γ] [Fintype Δ] [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R]

theorem native_certificate (D : NativeExperiments M I X R Γ Δ) {n : ℕ}
    (a b : D.protocol.State n)
    {left right : Witness ((D.protocol.fiber a.profile).spectralChecks.map MonomialTest.row)}
    {answer : Bool}
    (h : checkPair ((D.protocol.fiber a.profile).spectralChecks.map MonomialTest.row)
      a.law.spectrum b.law.spectrum left right = some answer) :
    D.protocol.Factorable a b ↔ a.profile ≤ b.profile ∧ answer = true := by
  rw [D.exact_six_iff]
  exact and_congr_right (fun _ => (checkPair_signature h).symm)

end Native

end CoreCertificate
end MovingProjection
