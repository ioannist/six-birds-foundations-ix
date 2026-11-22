import MovingProjection.Classification
import Mathlib.Data.Fintype.BigOperators

/-!
Local rational connectivity of positive normalized rate laws under homogeneous
protected monomial tests. Inverse coordinates turn the lower cutoffs into
magnitude budgets in the same signed-chart theorem.
-/

namespace MovingProjection

open scoped BigOperators

variable {M : Type*} [Fintype M] [DecidableEq M]

def RateLegal (δ : ℚ) (tests : List (MonomialTest M)) (x : M → ℚ) : Prop :=
  (∀ m, δ ≤ x m) ∧ (∑ m, x m) = 1 ∧ ∀ r ∈ tests, r.holds x

private def augmentRates (x : M → ℚ) : M ⊕ M → ℚ :=
  Sum.elim x (fun m => (x m)⁻¹)

private def extendExponent (e : M → ℕ) : M ⊕ M → ℕ :=
  Sum.elim e (fun _ => 0)

private def extendTest (r : MonomialTest M) : MonomialTest (M ⊕ M) :=
  ⟨⟨extendExponent r.row.lhs, extendExponent r.row.rhs⟩, r.ratio⟩

private def inverseTest (m : M) : MonomialTest (M ⊕ M) :=
  ⟨⟨Sum.elim (fun n => if n = m then 1 else 0) (fun n => if n = m then 1 else 0),
    fun _ => 0⟩, 1⟩

private noncomputable def extendedTests (tests : List (MonomialTest M)) : List (MonomialTest (M ⊕ M)) :=
  tests.map extendTest ++ Finset.univ.toList.map inverseTest

private def rateBudget : MarkBudget (M ⊕ M) :=
  ⟨Finset.univ.map Function.Embedding.inl, 1⟩

private def inverseBudget (δ : ℚ) (m : M) : MarkBudget (M ⊕ M) :=
  ⟨{Sum.inr m}, δ⁻¹⟩

private noncomputable def extendedBudgets (δ : ℚ) : List (MarkBudget (M ⊕ M)) :=
  rateBudget :: Finset.univ.toList.map (inverseBudget δ)

omit [DecidableEq M] in
private theorem monomial_left (e : M → ℕ) (v : M ⊕ M → ℚ) :
    monomial (extendExponent e) v = monomial e (fun m => v (.inl m)) := by
  unfold monomial
  rw [Fintype.prod_sum_type]
  simp [extendExponent]

private theorem inverse_holds (m : M) (v : M ⊕ M → ℚ) :
    (inverseTest m).holds v ↔ v (.inl m) * v (.inr m) = 1 := by
  simp [inverseTest, MonomialTest.holds, monomial, Fintype.prod_sum_type]

private theorem augment_legal {δ : ℚ} {tests : List (MonomialTest M)} {x : M → ℚ}
    (hδ : 0 < δ) (hx : RateLegal δ tests x) :
    Legal (extendedTests tests) (extendedBudgets δ) (augmentRates x) := by
  have hp (m : M) := hδ.trans_le (hx.1 m)
  refine ⟨?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp h
      simpa [MonomialTest.holds, extendTest, monomial_left, augmentRates] using hx.2.2 r₀ hr₀
    · obtain ⟨m, _, rfl⟩ := List.mem_map.mp h
      rw [inverse_holds]
      exact mul_inv_cancel₀ (hp m).ne'
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hh
    · simp only [rateBudget, Finset.sum_map, Function.Embedding.inl_apply, augmentRates,
        Sum.elim_inl, abs_of_pos (hp _)]
      rw [hx.2.1]
    · obtain ⟨m, _, rfl⟩ := List.mem_map.mp hh
      simp only [inverseBudget, Finset.sum_singleton, augmentRates, Sum.elim_inr,
        abs_of_pos (inv_pos.mpr (hp m))]
      exact inv_le_inv₀ (hp m) hδ |>.2 (hx.1 m)

private def rawRates (v : M ⊕ M → ℚ) (m : M) : ℚ := |v (.inl m)|

private def normalized (v : M ⊕ M → ℚ) (m : M) : ℚ :=
  rawRates v m / ∑ n, rawRates v n

private theorem raw_lower {δ : ℚ} {tests : List (MonomialTest M)} {v : M ⊕ M → ℚ}
    (hδ : 0 < δ) (hv : Legal (extendedTests tests) (extendedBudgets δ) v) (m : M) :
    δ ≤ rawRates v m := by
  have hi : inverseTest m ∈ extendedTests tests := by simp [extendedTests]
  have htest := (inverse_holds m v).1 (hv.1 _ hi)
  have hb : inverseBudget δ m ∈ (extendedBudgets δ : List (MarkBudget (M ⊕ M))) := by
    simp [extendedBudgets]
  have hc : |v (.inr m)| ≤ δ⁻¹ := by simpa [inverseBudget] using hv.2 _ hb
  have hmul : rawRates v m * |v (.inr m)| = 1 := by
    rw [rawRates, ← abs_mul, htest, abs_one]
  have hh : 1 ≤ rawRates v m * δ⁻¹ := hmul ▸
    mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  rw [← div_eq_mul_inv] at hh
  exact (by simpa using (le_div_iff₀ hδ).mp hh)

private theorem raw_sum_le {δ : ℚ} {tests : List (MonomialTest M)} {v : M ⊕ M → ℚ}
    (hv : Legal (extendedTests tests) (extendedBudgets δ) v) :
    ∑ m, rawRates v m ≤ 1 := by
  have hb : (rateBudget : MarkBudget (M ⊕ M)) ∈ extendedBudgets δ := by simp [extendedBudgets]
  simpa [rateBudget, rawRates] using hv.2 _ hb

private theorem raw_sum_lower [Nonempty M] {δ : ℚ} {tests : List (MonomialTest M)}
    {v : M ⊕ M → ℚ} (hδ : 0 < δ)
    (hv : Legal (extendedTests tests) (extendedBudgets δ) v) :
    δ ≤ ∑ m, rawRates v m := by
  let m : M := Classical.choice inferInstance
  exact (raw_lower hδ hv m).trans (Finset.single_le_sum
    (fun i _ => abs_nonneg (v (.inl i))) (Finset.mem_univ m))

omit [DecidableEq M] in
private theorem monomial_abs (e : M → ℕ) (x : M → ℚ) :
    monomial e (fun m => |x m|) = |monomial e x| := by
  unfold monomial
  rw [Finset.abs_prod]
  simp [abs_pow]

private theorem normalization_legal [Nonempty M] {δ : ℚ} {tests : List (MonomialTest M)}
    (hδ : 0 < δ)
    (hom : ∀ r ∈ tests, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ tests, 0 < r.ratio)
    {v : M ⊕ M → ℚ} (hv : Legal (extendedTests tests) (extendedBudgets δ) v) :
    RateLegal δ tests (normalized v) := by
  let S := ∑ m, rawRates v m
  have hS : 0 < S := hδ.trans_le (raw_sum_lower hδ hv)
  have hb := raw_sum_le hv
  refine ⟨?_, ?_, ?_⟩
  · intro m
    change δ ≤ rawRates v m / S
    apply (le_div_iff₀ hS).2
    exact (mul_le_of_le_one_right hδ.le hb).trans (raw_lower hδ hv m)
  · change (∑ m, rawRates v m / S) = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hS.ne'
  · intro r hr
    have ht : extendTest r ∈ extendedTests tests :=
      List.mem_append_left _ (List.mem_map_of_mem hr)
    have h := hv.1 _ ht
    have h₀ : monomial r.row.lhs (fun m => v (.inl m)) =
        r.ratio * monomial r.row.rhs (fun m => v (.inl m)) := by
      simpa [MonomialTest.holds, extendTest, monomial_left] using h
    have h₁ : monomial r.row.lhs (rawRates v) = r.ratio * monomial r.row.rhs (rawRates v) := by
      unfold rawRates
      rw [monomial_abs, monomial_abs, h₀, abs_mul, abs_of_pos (pos r hr)]
    change monomial r.row.lhs (fun m => rawRates v m * S⁻¹) =
      r.ratio * monomial r.row.rhs (fun m => rawRates v m * S⁻¹)
    rw [monomial_mul, monomial_mul, h₁, mul_assoc]
    congr 2
    simp only [monomial, Finset.prod_pow_eq_pow_sum, hom r hr]

def RateStep (δ : ℚ) (tests : List (MonomialTest M)) (ε : ℚ)
    (x y : M → ℚ) : Prop :=
  RateLegal δ tests x ∧ RateLegal δ tests y ∧ ∀ m, |x m - y m| < ε

omit [DecidableEq M] in
private theorem normalized_augment {δ : ℚ} {tests : List (MonomialTest M)} {x : M → ℚ}
    (hδ : 0 < δ) (h : RateLegal δ tests x) : normalized (augmentRates x) = x := by
  funext m
  have hp (k : M) : 0 < x k := hδ.trans_le (h.1 k)
  simp only [normalized, rawRates, augmentRates, Sum.elim_inl, abs_of_pos (hp _), h.2.1, div_one]

private theorem normalized_step [Nonempty M] {δ : ℚ} {tests : List (MonomialTest M)} {ε : ℚ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hom : ∀ r ∈ tests, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ tests, 0 < r.ratio)
    {x y : M ⊕ M → ℚ}
    (h : LocalStep (extendedTests tests) (extendedBudgets δ)
      (δ * ε / ((Fintype.card M : ℚ) + 2)) x y) :
    RateStep δ tests ε (normalized x) (normalized y) := by
  let S := ∑ m, rawRates x m
  let T := ∑ m, rawRates y m
  let d := δ * ε / ((Fintype.card M : ℚ) + 2)
  have hd : 0 < d := by unfold d; positivity
  have hS : 0 < S := hδ.trans_le (raw_sum_lower hδ h.1)
  have hT : 0 < T := hδ.trans_le (raw_sum_lower hδ h.2.1)
  have hdiff (m : M) : |rawRates x m - rawRates y m| < d := by
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans_lt (h.2.2 (.inl m))
  have hsum : |T-S| ≤ (Fintype.card M : ℚ) * d := by
    unfold S T
    rw [abs_sub_comm, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using Finset.sum_le_sum (s := (Finset.univ : Finset M)) (fun m _ => (hdiff m).le))
  refine ⟨normalization_legal hδ hom pos h.1, normalization_legal hδ hom pos h.2.1, fun m => ?_⟩
  have hy : 0 ≤ normalized y m := div_nonneg (abs_nonneg _) hT.le
  have hy₁ : normalized y m ≤ 1 := by
    change rawRates y m / T ≤ 1
    apply (div_le_iff₀ hT).2
    simpa only [one_mul] using
      (Finset.single_le_sum (fun i _ => abs_nonneg (y (.inl i))) (Finset.mem_univ m))
  have heq : normalized x m - normalized y m =
      (rawRates x m - rawRates y m + (T-S)*normalized y m) / S := by
    change rawRates x m / S - rawRates y m / T =
      (rawRates x m - rawRates y m + (T-S)*(rawRates y m / T)) / S
    field_simp
    ring
  have hnum : |rawRates x m - rawRates y m + (T-S)*normalized y m| <
      ((Fintype.card M : ℚ)+1)*d := by
    apply (abs_add_le _ _).trans_lt
    rw [abs_mul, abs_of_nonneg hy]
    have HH := (mul_le_of_le_one_right (abs_nonneg (T-S)) hy₁).trans hsum
    linarith [hdiff m]
  rw [heq, abs_div, abs_of_pos hS]
  apply (div_lt_iff₀ hS).2
  have hmul := mul_le_mul_of_nonneg_left (raw_sum_lower hδ h.1) hε.le
  have hds : ((Fintype.card M : ℚ)+2)*d = δ*ε := by unfold d; field_simp
  apply hnum.trans_le
  linarith

theorem rate_fineConnected [Nonempty M] {δ : ℚ} {tests : List (MonomialTest M)}
    (hδ : 0 < δ)
    (hom : ∀ r ∈ tests, (∑ m, r.row.lhs m) = ∑ m, r.row.rhs m)
    (pos : ∀ r ∈ tests, 0 < r.ratio)
    {x y : M → ℚ} (hx : RateLegal δ tests x) (hy : RateLegal δ tests y) :
    ∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (RateStep δ tests ε) x y := by
  have hsign : signCode (embed (augmentRates x)) = signCode (embed (augmentRates y)) := by
    funext i
    have hp (a : M → ℚ) (ha : RateLegal δ tests a) : 0 < (embed (augmentRates a) i) := by
      have h (m : M) := hδ.trans_le (ha.1 m)
      cases i with
      | inl m =>
        change 0 < (a m : ℝ)
        exact_mod_cast h m
      | inr m =>
        change 0 < (((a m)⁻¹ : ℚ) : ℝ)
        exact_mod_cast inv_pos.mpr (h m)
    exact (sign_pos (hp x hx)).trans (sign_pos (hp y hy)).symm
  have hchart := fineConnected_same_chart (augment_legal hδ hx) (augment_legal hδ hy) hsign
  intro ε hε
  let η := δ * ε / ((Fintype.card M : ℚ) + 2)
  have hη : 0 < η := by unfold η; positivity
  have hpath := hchart η hη
  have hmap : Relation.ReflTransGen (RateStep δ tests ε)
      (normalized (augmentRates x)) (normalized (augmentRates y)) :=
    hpath.lift normalized (fun _ _ h => normalized_step hδ hε hom pos h)
  simpa only [normalized_augment hδ hx, normalized_augment hδ hy] using hmap

end MovingProjection
