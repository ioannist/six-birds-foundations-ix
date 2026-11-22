import MovingProjection.ParityKernel
import Mathlib.Data.Fintype.BigOperators

/-!
The conditional register lift of the projected parity kernel.
The blocks below may depend on both the source and destination base states.
-/

namespace MovingProjection

open scoped BigOperators

variable {I X R M : Type*}
  [Fintype I] [Fintype X] [Fintype R] [Fintype M] [DecidableEq I]

def nativeMarked (b : ParityBasis I X) (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (m : M) (s t : X × R) : ℚ :=
  rate m * b.kernel (spectra m) s.1 t.1 * reg m s.1 t.1 s.2 t.2

def nativeStationary (ν : R → ℚ) (s : X × R) : ℚ :=
  ν s.2 / (Fintype.card X : ℚ)

omit [Fintype M] [Fintype R] in
theorem native_block_test (b : ParityBasis I X) (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ) (m : M) (x y : X) (u : R)
    (block : Finset R) (p : ℚ) (h : ∑ v ∈ block, reg m x y u v = p) :
    ∑ v ∈ block, nativeMarked b spectra rate reg m (x,u) (y,v) =
      rate m * b.kernel (spectra m) x y * p := by
  simp only [nativeMarked]
  rw [← Finset.mul_sum, h]

omit [Fintype M] in
theorem native_projection (b : ParityBasis I X) (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ) (m : M) (x y : X) (u : R)
    (h : ∑ v, reg m x y u v = 1) :
    ∑ v, nativeMarked b spectra rate reg m (x,u) (y,v) =
      rate m * b.kernel (spectra m) x y := by
  simpa only [mul_one] using native_block_test b spectra rate reg m x y u Finset.univ 1 h

theorem native_row_sum (b : ParityBasis I X) [Nonempty X] (spectra : M → I → ℚ)
    (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (hRate : ∑ m, rate m = 1) (hReg : ∀ m x y u, ∑ v, reg m x y u v = 1)
    (s : X × R) :
    ∑ m, ∑ t, nativeMarked b spectra rate reg m s t = 1 := by
  rcases s with ⟨x,u⟩
  calc
    _ = ∑ m, rate m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Fintype.sum_prod_type]
      simp_rw [native_projection _ _ _ _ _ _ _ _ (hReg _ _ _ _)]
      rw [← Finset.mul_sum, b.kernel_row_sum, mul_one]
    _ = _ := hRate

omit [Fintype M] [Fintype R] in
theorem native_reverse (b : ParityBasis I X)
    (spectra : M → I → ℚ) (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (rev : M → M) (ν : R → ℚ) (m : M) (s t : X × R)
    (hSpectra : spectra m = spectra (rev m))
    (hPair : ν s.2 * reg m s.1 t.1 s.2 t.2 =
      ν t.2 * reg (rev m) t.1 s.1 t.2 s.2) :
    nativeStationary ν s * nativeMarked b spectra rate reg m s t * rate (rev m) =
      nativeStationary ν t * nativeMarked b spectra rate reg (rev m) t s * rate m := by
  unfold nativeStationary nativeMarked
  calc
    _ = (rate m * rate (rev m) * b.kernel (spectra m) s.1 t.1 /
            (Fintype.card X : ℚ)) * (ν s.2 * reg m s.1 t.1 s.2 t.2) := by ring
    _ = _ := by
      rw [hPair, hSpectra, b.kernel_symm (spectra (rev m)) s.1 t.1]
      ring

theorem native_stationarity (b : ParityBasis I X) [Nonempty X]
    (spectra : M → I → ℚ) (rate : M → ℚ) (reg : M → X → X → R → R → ℚ)
    (ν : R → ℚ) (hRate : ∑ m, rate m = 1)
    (hReg : ∀ m x y v, ∑ u, ν u * reg m x y u v = ν v)
    (t : X × R) :
    ∑ m, ∑ s, nativeStationary ν s * nativeMarked b spectra rate reg m s t =
      nativeStationary ν t := by
  rcases t with ⟨y,v⟩
  have inner (m : M) (x : X) :
      (∑ u, nativeStationary ν (x,u) *
        nativeMarked b spectra rate reg m (x,u) (y,v)) =
        (rate m * b.kernel (spectra m) x y / (Fintype.card X : ℚ)) * ν v := by
    rw [← hReg m x y v, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp only [nativeStationary, nativeMarked]
    ring
  have column (m : M) : ∑ x, b.kernel (spectra m) x y = 1 := by
    simpa only [b.kernel_symm (spectra m) y] using b.kernel_row_sum (spectra m) y
  have step (m : M) :
      (∑ s, nativeStationary ν s * nativeMarked b spectra rate reg m s (y,v)) =
        rate m * nativeStationary ν (y,v) := by
    rw [Fintype.sum_prod_type]
    simp_rw [inner]
    simp only [nativeStationary]
    calc
      _ = (rate m * (ν v / (Fintype.card X : ℚ))) *
          ∑ x, b.kernel (spectra m) x y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [column, mul_one]
  simp_rw [step]
  rw [← Finset.sum_mul, hRate, one_mul]

end MovingProjection
