import MovingProjection.ParityKernel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log

/-! Balanced, orthogonal binary characters with enough labels on
a base of size linear in the number of probes. -/

namespace MovingProjection.BinaryParity

open scoped BigOperators

abbrev Base (d : ℕ) := Fin d → Bool

def character {d : ℕ} (a x : Base d) : ℚ :=
  ∏ j, if a j && x j then -1 else 1

private def flip {d : ℕ} (i : Fin d) (x : Base d) : Base d :=
  fun j => if j = i then !(x j) else x j

private def flipEquiv {d : ℕ} (i : Fin d) : Base d ≃ Base d where
  toFun := flip i
  invFun := flip i
  left_inv := fun x => by funext j; by_cases h : j = i <;> simp [flip, h]
  right_inv := fun x => by funext j; by_cases h : j = i <;> simp [flip, h]

private theorem character_sq {d : ℕ} (a x : Base d) : character a x * character a x = 1 := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  cases a j <;> cases x j <;> norm_num

private theorem character_abs {d : ℕ} (a x : Base d) : |character a x| = 1 := by
  have h := character_sq a x
  rcases le_total 0 (character a x) with hp | hn
  · rw [abs_of_nonneg hp]
    nlinarith [sq_nonneg (character a x - 1)]
  · rw [abs_of_nonpos hn]
    nlinarith [sq_nonneg (character a x + 1)]

private theorem character_product {d : ℕ} (a b x : Base d) :
    character a x * character b x = character (fun j => a j != b j) x := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases ha : a j <;> cases hb : b j <;> cases hx : x j <;> norm_num [ha, hb, hx]

private theorem character_flip {d : ℕ} (a x : Base d) (i : Fin d) (hi : a i = true) :
    character a (flip i x) = -character a x := by
  let factor (x : Base d) (j : Fin d) : ℚ := if a j && x j then -1 else 1
  change (∏ j, factor (flip i x) j) = -(∏ j, factor x j)
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have h : (∏ j ∈ Finset.univ.erase i, factor (flip i x) j) =
      ∏ j ∈ Finset.univ.erase i, factor x j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [factor, flip, (Finset.mem_erase.mp hj).1]
  rw [h]
  cases hx : x i <;> simp [flip, factor, hi, hx]

private theorem character_balance {d : ℕ} (a : Base d) (ha : a ≠ fun _ => false) :
    ∑ x, character a x = 0 := by
  classical
  have he : ∃ i, a i = true := by
    by_contra! hn
    apply ha
    funext j
    cases h : a j <;> simp_all
  obtain ⟨i, hi⟩ := he
  have hf := Fintype.sum_equiv (flipEquiv i) (fun x => -character a x) (character a)
    (fun x => (character_flip a x i hi).symm)
  rw [Finset.sum_neg_distrib] at hf
  linarith

variable {I : Type*} [DecidableEq I]

def ofLabels {d : ℕ} (a : I ↪ {x : Base d // x ≠ fun _ => false}) : ParityBasis I (Base d) where
  value i := character (a i).1
  abs_eq_one i := character_abs (a i).1
  balance i := character_balance (a i).1 (a i).2
  orthogonal i j := by
    by_cases h : i = j
    · subst j
      simp [character_sq]
    · have ha : (fun k => (a i).1 k != (a j).1 k) ≠ (fun _ => false) := by
        intro he
        apply h (a.injective (Subtype.ext ?_))
        funext k
        have hk := congrFun he k
        simpa using hk
      rw [if_neg h]
      simp_rw [character_product]
      exact character_balance _ ha

variable [Fintype I]

def dimension (I : Type*) [Fintype I] : ℕ := Nat.clog 2 (Fintype.card I + 1)

theorem card_base (d : ℕ) : Fintype.card (Base d) = 2 ^ d := by
  simp [Base, Fintype.card_pi]

private theorem card_nonzero (d : ℕ) :
    Fintype.card {x : Base d // x ≠ fun _ => false} = 2 ^ d - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun x : Base d => x = fun _ => false),
    Fintype.card_subtype_eq, card_base]

noncomputable def basis : ParityBasis I (Base (dimension I)) := by
  classical
  let L := {x : Base (dimension I) // x ≠ fun _ => false}
  have hc : Fintype.card I ≤ Fintype.card L := by
    dsimp only [L]
    rw [card_nonzero]
    have h := Nat.le_pow_clog (b := 2) (by decide) (Fintype.card I + 1)
    exact Nat.le_sub_of_add_le h
  exact ofLabels ((Fintype.equivFin I).toEmbedding.trans
    ((Fin.castLEEmb hc).trans (Fintype.equivFin L).symm.toEmbedding))

omit [DecidableEq I] in
theorem size_bounds [Nonempty I] :
    Fintype.card I + 1 ≤ Fintype.card (Base (dimension I)) ∧
      Fintype.card (Base (dimension I)) < 2 * (Fintype.card I + 1) := by
  rw [card_base]
  have hI : 1 < Fintype.card I + 1 := by have := Fintype.card_pos (α := I); omega
  refine ⟨Nat.le_pow_clog (by decide) _, ?_⟩
  have hpos := Nat.clog_pos (b := 2) (by decide) hI
  have hs : dimension I = (dimension I).pred.succ := (Nat.succ_pred_eq_of_pos hpos).symm
  calc
    2 ^ dimension I = 2 ^ (dimension I).pred * 2 := by
      conv_lhs => rw [hs, Nat.pow_succ]
    _ < _ := by
      rw [Nat.mul_comm 2]
      exact Nat.mul_lt_mul_of_pos_right (Nat.pow_pred_clog_lt_self (by decide) hI) (by decide)

end MovingProjection.BinaryParity
