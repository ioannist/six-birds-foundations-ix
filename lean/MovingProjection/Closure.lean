import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

/-!
A real closure collision yields a strictly positive vector in the homogeneous
system on the vanishing coordinates. A linear section of the range removes
the bounded residual left by the surviving coordinates.
-/

namespace MovingProjection

open Filter

variable {I J α : Type*} [Fintype I] [Fintype J]

theorem positive_kernel_of_divergence (A : (I → ℝ) →ₗ[ℝ] (J → ℝ))
    {l : Filter α} [l.NeBot] {u : α → I → ℝ}
    (hu : ∀ i, Tendsto (fun a => u a i) l atBot)
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l, ‖A (u a)‖ ≤ C) :
    ∃ w : I → ℝ, A w = 0 ∧ ∀ i, 0 < w i := by
  obtain ⟨C, hC, hbound⟩ := hA
  obtain ⟨B, hB⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  let Bc : A.range →L[ℝ] (I → ℝ) := LinearMap.toContinuousLinearMap B
  let K := ‖Bc‖ * C
  have hu' : ∀ᶠ a in l, ∀ i : I, u a i < -K :=
    eventually_all.2 fun i => (hu i).eventually_lt_atBot _
  obtain ⟨a, ha, hb⟩ := (hu'.and hbound).exists
  let b : A.range := A.rangeRestrict (u a)
  have hb' : ‖b‖ ≤ C := hb
  have hnorm : ‖Bc b‖ ≤ K :=
    (Bc.le_opNorm b).trans (mul_le_mul_of_nonneg_left hb' (norm_nonneg Bc))
  refine ⟨Bc b - u a, ?_, ?_⟩
  · rw [map_sub]
    have heq : A.rangeRestrict (B b) = b := by
      exact LinearMap.congr_fun hB b
    have heq' : A (Bc b) = A (u a) :=
      congrArg (fun v : A.range => (v : J → ℝ)) heq
    rw [heq', sub_self]
  · intro i
    have hi : |Bc b i| ≤ K := (norm_le_pi_norm (Bc b) i).trans hnorm
    have hi' := (abs_le.mp hi).1
    change 0 < Bc b i - u a i
    linarith [ha i]

end MovingProjection
