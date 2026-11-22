import MovingProjection.Spectral
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
Finite orthogonal parity probes and the measured endpoint law of a word.
The proofs use only balance and orthogonality of the supplied parity probes.
-/

namespace MovingProjection

open scoped BigOperators

variable {I X M : Type*} [Fintype I] [Fintype X] [DecidableEq I]

structure ParityBasis (I X : Type*) [Fintype X] [DecidableEq I] where
  value : I → X → ℚ
  abs_eq_one : ∀ i x, |value i x| = 1
  balance : ∀ i, ∑ x, value i x = 0
  orthogonal : ∀ i j, ∑ x, value i x * value j x =
    if i = j then (Fintype.card X : ℚ) else 0

namespace ParityBasis

def kernel (b : ParityBasis I X) (spectrum : I → ℚ) (x y : X) : ℚ :=
  (1 + ∑ i, (spectrum i * b.value i x) * b.value i y) / (Fintype.card X : ℚ)

theorem kernel_symm (b : ParityBasis I X) (spectrum : I → ℚ) (x y : X) :
    b.kernel spectrum x y = b.kernel spectrum y x := by
  unfold kernel
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernel_pos (b : ParityBasis I X) [Nonempty X] (spectrum : I → ℚ)
    (h : (∑ i, |spectrum i|) < 1) (x y : X) :
    0 < b.kernel spectrum x y := by
  have hsum : |∑ i, (spectrum i * b.value i x) * b.value i y| < 1 := by
    apply lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) _
    simpa only [abs_mul, b.abs_eq_one, mul_one] using h
  have hn : 0 < (Fintype.card X : ℚ) := by exact_mod_cast Fintype.card_pos
  exact div_pos (by have hl := (abs_lt.mp hsum).1; linarith) hn

theorem kernel_apply (b : ParityBasis I X) (spectrum : I → ℚ) (x : X) (f : X → ℚ) :
    (∑ y, b.kernel spectrum x y * f y) =
      ((∑ y, f y) + ∑ i, (spectrum i * b.value i x) * (∑ y, b.value i y * f y)) /
        (Fintype.card X : ℚ) := by
  unfold kernel
  simp only [div_eq_mul_inv]
  calc
    _ = (∑ y, (1 + ∑ i, (spectrum i * b.value i x) * b.value i y) * f y) *
        (Fintype.card X : ℚ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      congr 1
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem kernel_row_sum (b : ParityBasis I X) [Nonempty X] (spectrum : I → ℚ) (x : X) :
    ∑ y, b.kernel spectrum x y = 1 := by
  have hn : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa [b.balance, hn] using b.kernel_apply spectrum x (fun _ => 1)

theorem kernel_response (b : ParityBasis I X) [Nonempty X]
    (spectrum : I → ℚ) (x : X) (i : I) :
    (∑ y, b.kernel spectrum x y * b.value i y) = spectrum i * b.value i x := by
  have hn : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [b.kernel_apply, b.balance, zero_add]
  simp only [b.orthogonal, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_div_cancel_right₀ _ hn]

theorem kernel_comp (b : ParityBasis I X) [Nonempty X]
    (spectrum other : I → ℚ) (x z : X) :
    (∑ y, b.kernel spectrum x y * b.kernel other y z) =
      b.kernel (fun i => spectrum i * other i) x z := by
  rw [b.kernel_apply]
  have hrow : (∑ y, b.kernel other y z) = 1 := by
    simpa only [b.kernel_symm other z] using b.kernel_row_sum other z
  have hr (i : I) : (∑ y, b.value i y * b.kernel other y z) = other i * b.value i z := by
    have hh := b.kernel_response other z i
    rw [← hh]
    apply Finset.sum_congr rfl
    intro y _
    rw [b.kernel_symm other y z, mul_comm]
  rw [hrow]
  simp_rw [hr]
  unfold kernel
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem kernel_eq_iff (b : ParityBasis I X) [Nonempty X] (s t : I → ℚ) :
    b.kernel s = b.kernel t ↔ s = t := by
  classical
  constructor
  · intro h
    let x : X := Classical.choice inferInstance
    funext i
    have hresp := b.kernel_response s x i
    rw [h, b.kernel_response] at hresp
    have hnonzero : b.value i x ≠ 0 := by
      intro hz
      have h₁ := b.abs_eq_one i x
      simp [hz] at h₁
    exact mul_right_cancel₀ hnonzero hresp.symm
  · rintro rfl
    rfl

/-- Nonempty timed word product of conditional projected kernels. -/
def nonemptyWord (b : ParityBasis I X) (law : M → I → ℚ) (first : M) :
    List M → X → X → ℚ
  | [] => b.kernel (law first)
  | m :: rest => fun x z =>
      ∑ y, b.kernel (law first) x y * b.nonemptyWord law m rest y z

theorem nonemptyWord_eq (b : ParityBasis I X) [Nonempty X]
    (law : M → I → ℚ) (first : M) (rest : List M) :
    b.nonemptyWord law first rest =
      b.kernel (fun i => ((first :: rest).map (fun m => law m i)).prod) := by
  induction rest generalizing first with
  | nil => simp [nonemptyWord]
  | cons m rest ih =>
    funext x z
    simp only [nonemptyWord, ih m, kernel_comp]
    rfl

theorem word_identity_iff (b : ParityBasis I X) [Nonempty X]
    (law : M → I → ℚ) (first next : M) (tail other : List M) :
    b.nonemptyWord law first tail = b.nonemptyWord law next other ↔
      ∀ i, ((first :: tail).map (fun m => law m i)).prod =
        ((next :: other).map (fun m => law m i)).prod := by
  rw [b.nonemptyWord_eq, b.nonemptyWord_eq, b.kernel_eq_iff]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

end ParityBasis

end MovingProjection
