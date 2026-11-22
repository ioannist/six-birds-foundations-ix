import MovingProjection.Contraction
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A protected length-two word identity disconnects two exact marked laws. -/

namespace MovingProjection.BinaryObstruction

open scoped BigOperators

def kernel (s : ℚ) (i j : Fin 2) : ℚ :=
  if i = j then (1+s)/2 else (1-s)/2

theorem kernel_pos {s : ℚ} (hs : |s| ≤ 1/2) (i j : Fin 2) : 0 < kernel s i j := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hs
  unfold kernel
  split <;> linarith

theorem kernel_symmetric (s : ℚ) (i j : Fin 2) : kernel s i j = kernel s j i := by
  simp [kernel, eq_comm]

theorem kernel_row_sum (s : ℚ) (i : Fin 2) : ∑ j, kernel s i j = 1 := by
  fin_cases i <;> simp [kernel, Fin.sum_univ_two] <;> ring

theorem kernel_comp (s t : ℚ) (i k : Fin 2) :
    ∑ j, kernel s i j * kernel t j k = kernel (s*t) i k := by
  fin_cases i <;> fin_cases k <;> simp [kernel, Fin.sum_univ_two] <;> ring

def wordIdentity (a b : ℚ) : Prop :=
  ∀ i k, (∑ j, kernel a i j * kernel a j k) = ∑ j, kernel b i j * kernel b j k

theorem wordIdentity_iff (a b : ℚ) : wordIdentity a b ↔ a*a = b*b := by
  constructor
  · intro h
    have h₀ := h 0 0
    rw [kernel_comp, kernel_comp] at h₀
    simp [kernel] at h₀
    linarith
  · intro h i j
    simp only [kernel_comp, h]

/-- Both marks have rate 1/2. Audit keeps the measured response of mark b at 1/4. -/
def held (x : ℚ × ℚ) : Prop :=
  |x.1| ≤ 1/2 ∧ |x.2| ≤ 1/2 ∧ x.2 = 1/4 ∧ wordIdentity x.1 x.2

def positiveLaw : ℚ × ℚ := (1/4, 1/4)
def negativeLaw : ℚ × ℚ := (-1/4, 1/4)

theorem held_two_laws {x : ℚ × ℚ} (hx : held x) :
    x = positiveLaw ∨ x = negativeLaw := by
  rcases x with ⟨a,b⟩
  rcases hx with ⟨_, _, hb, hw⟩
  change b = 1/4 at hb
  subst b
  have h := (wordIdentity_iff _ _).mp hw
  have hprod : (a-1/4)*(a+1/4) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hpos | hneg
  · have : a = 1/4 := by linarith
    simp [positiveLaw, this]
  · have : a = -1/4 := by linarith
    simp [negativeLaw, this]

theorem positiveLaw_held : held positiveLaw := by
  norm_num [held, positiveLaw, wordIdentity_iff]

theorem negativeLaw_held : held negativeLaw := by
  norm_num [held, negativeLaw, wordIdentity_iff]

/-- A necessary physical smallness test for a numerical step at native rate 1/2. -/
def localStep (ε : ℚ) (x y : ℚ × ℚ) : Prop :=
  held x ∧ held y ∧ |kernel y.1 0 0 / 2 - kernel x.1 0 0 / 2| < ε

theorem localStep_fixes_law {x y : ℚ × ℚ}
    (h : localStep (1/8) x y) : x = y := by
  rcases h with ⟨hx, hy, hsmall⟩
  rcases held_two_laws hx with rfl | rfl <;> rcases held_two_laws hy with rfl | rfl
  · rfl
  · norm_num [positiveLaw, negativeLaw, kernel] at hsmall
  · norm_num [positiveLaw, negativeLaw, kernel] at hsmall
  · rfl

theorem no_local_chain :
    ¬ Relation.ReflTransGen (localStep (1/8)) positiveLaw negativeLaw := by
  intro h
  have stable (y : ℚ × ℚ) (hy : Relation.ReflTransGen (localStep (1/8)) positiveLaw y) :
      positiveLaw = y := by
    induction hy with
    | refl => rfl
    | tail _ hstep ih => exact ih.trans (localStep_fixes_law hstep)
  have hfirst := congrArg Prod.fst (stable _ h)
  norm_num [positiveLaw, negativeLaw] at hfirst

end MovingProjection.BinaryObstruction
