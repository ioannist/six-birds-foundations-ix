import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation

/-!
Integer contraction of sign supports for protected monomial equations.
A row imposes a weight equation only while all its factors remain nonzero.
-/

namespace MovingProjection

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

structure ExponentRow (I : Type*) where
  lhs : I → ℕ
  rhs : I → ℕ

def ExponentRow.active (r : ExponentRow I) (s : Finset I) : Prop :=
  ∀ i ∉ s, r.lhs i = 0 ∧ r.rhs i = 0

def Damping (rows : List (ExponentRow I)) (s : Finset I) (w : I → ℕ) : Prop :=
  (∀ i ∉ s, w i = 0) ∧
    ∀ r ∈ rows, r.active s →
      ∑ i, r.lhs i * w i = ∑ i, r.rhs i * w i

def Contracts (rows : List (ExponentRow I)) (s t : Finset I) : Prop :=
  ∃ w : I → ℕ, Damping rows s w ∧ t = s.filter (fun i => w i = 0)

omit [DecidableEq I] in
theorem Contracts.subset {rows : List (ExponentRow I)} {s t : Finset I}
    (h : Contracts rows s t) : t ⊆ s := by
  obtain ⟨w, _, rfl⟩ := h
  exact Finset.filter_subset _ _

theorem Contracts.restrict {rows : List (ExponentRow I)} {s t u : Finset I}
    (h : Contracts rows s t) (hu : u ⊆ s) : Contracts rows u (u ∩ t) := by
  classical
  obtain ⟨w, hw, rfl⟩ := h
  let v (i : I) := if i ∈ u then w i else 0
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    simp [v, hi]
  · intro r hr ha
    have ha' : r.active s := fun i hi => ha i (fun hm => hi (hu hm))
    have eqL : (∑ i, r.lhs i * v i) = ∑ i, r.lhs i * w i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ u
      · simp [v, hi]
      · simp [v, hi, (ha i hi).1]
    have eqR : (∑ i, r.rhs i * v i) = ∑ i, r.rhs i * w i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ u
      · simp [v, hi]
      · simp [v, hi, (ha i hi).2]
    exact eqL.trans ((hw.2 r hr ha').trans eqR.symm)
  · ext i
    simp only [Finset.mem_inter, Finset.mem_filter]
    by_cases hi : i ∈ u
    · simp [v, hi, hu hi]
    · simp [hi]

abbrev Reduces (rows : List (ExponentRow I)) :=
  Relation.ReflTransGen (Contracts rows)

omit [DecidableEq I] in
theorem Reduces.subset {rows : List (ExponentRow I)} {s t : Finset I}
    (h : Reduces rows s t) : t ⊆ s := by
  induction h with
  | refl => exact fun _ hi => hi
  | tail _ hstep ih => exact hstep.subset.trans ih

theorem Reduces.restrict {rows : List (ExponentRow I)} {s t u : Finset I}
    (h : Reduces rows s t) (hu : u ⊆ s) : Reduces rows u (u ∩ t) := by
  induction h with
  | refl =>
    have heq : u ∩ s = u := Finset.inter_eq_left.mpr hu
    rw [heq]
  | @tail v t _ hstep ih =>
    have hcontract := hstep.restrict (u := u ∩ v) Finset.inter_subset_right
    have heq : u ∩ v ∩ t = u ∩ t := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hstep.subset]
    rw [heq] at hcontract
    exact ih.tail hcontract

/-- The least reachable support, computed by dropping positive weights to zero. -/
def IsCore (rows : List (ExponentRow I)) (s c : Finset I) : Prop :=
  Reduces rows s c ∧ ∀ t, Reduces rows s t → c ⊆ t

theorem exists_core (rows : List (ExponentRow I)) (s : Finset I) :
    ∃ c, IsCore rows s c := by
  classical
  let P (n : ℕ) : Prop := ∃ c : Finset I, Reduces rows s c ∧ c.card = n
  have hp : ∃ n, P n := ⟨s.card, s, .refl, rfl⟩
  obtain ⟨c, hc, hcard⟩ := Nat.find_spec hp
  refine ⟨c, hc, fun t ht => ?_⟩
  have hmeet : Reduces rows s (t ∩ c) := ht.trans (hc.restrict ht.subset)
  have hmin : c.card ≤ (t ∩ c).card := by
    rw [hcard]
    exact Nat.find_min' hp ⟨t ∩ c, hmeet, rfl⟩
  have heq : t ∩ c = c := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hmin
  rw [← heq]
  exact Finset.inter_subset_left

omit [DecidableEq I] in
theorem IsCore.unique {rows : List (ExponentRow I)} {s c d : Finset I}
    (hc : IsCore rows s c) (hd : IsCore rows s d) : c = d :=
  Finset.Subset.antisymm (hc.2 d hd.1) (hd.2 c hc.1)

theorem IsCore.of_reduces {rows : List (ExponentRow I)} {s t c : Finset I}
    (hc : IsCore rows s c) (ht : Reduces rows s t) : IsCore rows t c := by
  refine ⟨?_, fun u hu => hc.2 u (ht.trans hu)⟩
  have h := hc.1.restrict ht.subset
  rwa [Finset.inter_eq_right.mpr (hc.2 t ht)] at h

noncomputable def core (rows : List (ExponentRow I)) (s : Finset I) : Finset I :=
  Classical.choose (exists_core rows s)

theorem isCore_core (rows : List (ExponentRow I)) (s : Finset I) :
    IsCore rows s (core rows s) :=
  Classical.choose_spec (exists_core rows s)

theorem core_eq_of_reduces {rows : List (ExponentRow I)} {s t : Finset I}
    (h : Reduces rows s t) : core rows s = core rows t :=
  ((isCore_core rows s).of_reduces h).unique (isCore_core rows t)

theorem core_eq_iff_common_reduct {rows : List (ExponentRow I)} {s t : Finset I} :
    core rows s = core rows t ↔ ∃ c, Reduces rows s c ∧ Reduces rows t c := by
  constructor
  · intro h
    refine ⟨core rows s, (isCore_core rows s).1, ?_⟩
    rw [h]
    exact (isCore_core rows t).1
  · rintro ⟨c, hsc, htc⟩
    exact (core_eq_of_reduces hsc).trans (core_eq_of_reduces htc).symm

end MovingProjection
