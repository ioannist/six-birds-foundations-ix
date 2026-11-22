import MovingProjection.NativeKernel

/-! Native one-step preparation probes recover rates and spectra, and control
spectral step size in the physical metric. -/

namespace MovingProjection

open scoped BigOperators

variable {I X R M : Type*}
  [Fintype I] [Fintype X] [Fintype R] [DecidableEq I]

def observedRate (P : M → X × R → X × R → ℚ) (m : M) (s : X × R) : ℚ :=
  ∑ t, P m s t

def observedSignal (b : ParityBasis I X) (P : M → X × R → X × R → ℚ)
    (m : M) (s : X × R) (i : I) : ℚ :=
  ∑ t, (P m s t * b.value i t.1) * b.value i s.1

omit [Fintype I] [DecidableEq I] in
theorem observedRate_sub_le (P Q : M → X × R → X × R → ℚ)
    (m : M) (s : X × R) {ε : ℚ} (h : ∀ t, |P m s t - Q m s t| ≤ ε) :
    |observedRate P m s - observedRate Q m s| ≤ (Fintype.card (X × R) : ℚ) * ε := by
  rw [observedRate, observedRate, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (X × R))) (fun t _ => h t))

omit [Fintype I] in
theorem observedSignal_sub_le (b : ParityBasis I X) (P Q : M → X × R → X × R → ℚ)
    (m : M) (s : X × R) (i : I) {ε : ℚ} (h : ∀ t, |P m s t - Q m s t| ≤ ε) :
    |observedSignal b P m s i - observedSignal b Q m s i| ≤
      (Fintype.card (X × R) : ℚ) * ε := by
  rw [observedSignal, observedSignal, ← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simp only [abs_mul, b.abs_eq_one, mul_one]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (X × R))) (fun t _ => h t))

theorem observedRate_native (b : ParityBasis I X) [Nonempty X] (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (hReg : ∀ m x y u, ∑ v, reg m x y u v = 1) (m : M) (s : X × R) :
    observedRate (nativeMarked b spectra rate reg) m s = rate m := by
  rcases s with ⟨x,u⟩
  unfold observedRate
  rw [Fintype.sum_prod_type]
  simp_rw [native_projection _ _ _ _ _ _ _ _ (hReg _ _ _ _)]
  rw [← Finset.mul_sum, b.kernel_row_sum, mul_one]

theorem observedSignal_native (b : ParityBasis I X) [Nonempty X] (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (hReg : ∀ m x y u, ∑ v, reg m x y u v = 1) (m : M) (s : X × R) (i : I) :
    observedSignal b (nativeMarked b spectra rate reg) m s i = rate m * spectra m i := by
  rcases s with ⟨x,u⟩
  unfold observedSignal
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul]
  simp_rw [native_projection _ _ _ _ _ _ _ _ (hReg _ _ _ _)]
  have H : (∑ t, rate m * b.kernel (spectra m) x t * b.value i t) =
      rate m * (∑ t, b.kernel (spectra m) x t * b.value i t) := by
    simp [mul_assoc, Finset.mul_sum]
  rw [H, b.kernel_response]
  have hsq : b.value i x * b.value i x = 1 := by
    rw [← sq, ← sq_abs, b.abs_eq_one]
    norm_num
  calc
    _ = (rate m * spectra m i) * (b.value i x * b.value i x) := by ring
    _ = _ := by rw [hsq, mul_one]

theorem native_spectral_modulus (b : ParityBasis I X) [Nonempty X]
    (a c : M → I → ℚ) (rate other : M → ℚ)
    (reg next : M → X → X → R → R → ℚ)
    (hReg : ∀ m x y u, ∑ v, reg m x y u v = 1)
    (hNext : ∀ m x y u, ∑ v, next m x y u v = 1)
    (m : M) (s : X × R) (i : I) {δ ε : ℚ} (hδ : 0 < δ) (hd : δ ≤ rate m)
    (hc : |c m i| ≤ 1)
    (h : ∀ t, |nativeMarked b a rate reg m s t -
      nativeMarked b c other next m s t| ≤ ε) :
    |a m i - c m i| ≤ (2 * (Fintype.card (X × R) : ℚ) * ε) / δ := by
  have hrate := observedRate_sub_le _ _ _ _ h
  rw [observedRate_native _ _ _ _ hReg, observedRate_native _ _ _ _ hNext] at hrate
  have hsignal := observedSignal_sub_le b _ _ _ _ i h
  rw [observedSignal_native _ _ _ _ hReg, observedSignal_native _ _ _ _ hNext] at hsignal
  have hf : rate m * (a m i - c m i) =
      (rate m * a m i - other m * c m i) + (other m - rate m) * c m i := by ring
  apply (le_div_iff₀ hδ).2
  calc
    _ ≤ |a m i - c m i| * rate m := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = |rate m * (a m i - c m i)| := by
        rw [abs_mul, abs_of_pos (hδ.trans_le hd), mul_comm]
    _ ≤ |rate m * a m i - other m * c m i| + |(other m - rate m) * c m i| := by
        rw [hf]
        exact abs_add_le _ _
    _ ≤ (Fintype.card (X × R) : ℚ) * ε + (Fintype.card (X × R) : ℚ) * ε := by
        apply add_le_add hsignal
        rw [abs_mul, abs_sub_comm]
        exact (mul_le_of_le_one_right (abs_nonneg _) hc).trans hrate
    _ = _ := by ring

end MovingProjection
