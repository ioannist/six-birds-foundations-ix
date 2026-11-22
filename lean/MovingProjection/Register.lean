import MovingProjection.NativeProbes
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A finite conditional register, with independently measured support and
terminal disclosure constraints. -/

namespace MovingProjection

open scoped BigOperators

variable {M X R : Type*} [Fintype R]

abbrev Register (M X R : Type*) := M → X → X → R → R → ℚ
abbrev Proposal (M X R : Type*) := M × X × X × R × R

def registerMask (L : Register M X R) : Set (Proposal M X R) :=
  {e | 0 < L e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2}

def Available (f : Setoid R) (d : R → Bool) : Prop :=
  ∀ u v, f.r u v → d u = d v

def RegisterValid (ν : R → ℚ) (rev : M → M)
    (f : Setoid R) (L : Register M X R) : Prop :=
  (∀ m x y u v, 0 ≤ L m x y u v) ∧
  (∀ m x y u, ∑ v, L m x y u v = 1) ∧
  (∀ m x y v, ∑ u, ν u * L m x y u v = ν v) ∧
  (∀ m x y u v, ν u * L m x y u v = ν v * L (rev m) y x v u) ∧
  ∀ m x y u d, Available f d →
    (∑ v, if d v then L m x y u v else 0) = ∑ v, if d v then ν v else 0

theorem RegisterValid.coarsen {ν : R → ℚ} {rev : M → M} {L : Register M X R}
    {f g : Setoid R} (h : RegisterValid ν rev g L) (hfg : g ≤ f) :
    RegisterValid ν rev f L := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro m x y u d hd
  exact h.2.2.2.2 m x y u d (fun v w hvw => hd v w (hfg hvw))

theorem RegisterValid.entry_le_one {ν : R → ℚ} {rev : M → M} {L : Register M X R}
    {f : Setoid R} (h : RegisterValid ν rev f L) (m : M) (x y : X) (u v : R) :
    L m x y u v ≤ 1 := by
  rw [← h.2.1 m x y u]
  exact Finset.single_le_sum (fun i _ => h.1 m x y u i) (Finset.mem_univ v)

def registerMix (L K : Register M X R) (t : ℚ) : Register M X R :=
  fun m x y u v => (1-t) * L m x y u v + t * K m x y u v

theorem RegisterValid.mix {ν : R → ℚ} {rev : M → M} {L K : Register M X R}
    {f : Setoid R} (hL : RegisterValid ν rev f L) (hK : RegisterValid ν rev f K)
    {t : ℚ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    RegisterValid ν rev f (registerMix L K t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m x y u v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht') (hL.1 _ _ _ _ _))
      (mul_nonneg ht (hK.1 _ _ _ _ _))
  · intro m x y u
    simp only [registerMix, Finset.sum_add_distrib, ← Finset.mul_sum, hL.2.1, hK.2.1]
    ring
  · intro m x y v
    have he (u : R) : ν u * registerMix L K t m x y u v =
        (1-t)*(ν u * L m x y u v) + t*(ν u * K m x y u v) := by
      unfold registerMix
      ring
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, hL.2.2.1, hK.2.2.1]
    ring
  · intro m x y u v
    calc
      _ = (1-t)*(ν u * L m x y u v) + t*(ν u * K m x y u v) := by
        unfold registerMix
        ring
      _ = _ := by
        rw [hL.2.2.2.1, hK.2.2.2.1]
        unfold registerMix
        ring
  · intro m x y u d hd
    have he (v : R) : (if d v then registerMix L K t m x y u v else 0) =
        (1-t)*(if d v then L m x y u v else 0) +
        t*(if d v then K m x y u v else 0) := by
      split <;> simp [registerMix, *]
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum,
      hL.2.2.2.2 _ _ _ _ _ hd, hK.2.2.2.2 _ _ _ _ _ hd]
    ring

theorem registerMix_mask {ν : R → ℚ} {rev : M → M} {L K : Register M X R}
    {f : Setoid R} (hL : RegisterValid ν rev f L) (hK : RegisterValid ν rev f K)
    (h : registerMask L = registerMask K) {t : ℚ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    registerMask (registerMix L K t) = registerMask L := by
  ext e
  rcases e with ⟨m,x,y,u,v⟩
  have he : 0 < L m x y u v ↔ 0 < K m x y u v :=
    Set.ext_iff.mp h (m,x,y,u,v)
  change 0 < (1-t)*L m x y u v + t*K m x y u v ↔ 0 < L m x y u v
  constructor
  · intro hpos
    by_contra hn
    have hl : L m x y u v = 0 := le_antisymm (le_of_not_gt hn) (hL.1 _ _ _ _ _)
    have hk : K m x y u v = 0 :=
      le_antisymm (le_of_not_gt fun hh => hn (he.mpr hh)) (hK.1 _ _ _ _ _)
    simp [hl, hk] at hpos
  · intro hl
    have hk := he.mp hl
    rcases eq_or_lt_of_le h₀ with rfl | ht
    · simpa using hl
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr h₁) hl.le) (mul_pos ht hk)

def RegisterStep (ν : R → ℚ) (rev : M → M) (f : Setoid R)
    (S : Set (Proposal M X R)) (ε : ℚ) (L K : Register M X R) : Prop :=
  RegisterValid ν rev f L ∧ RegisterValid ν rev f K ∧
    registerMask L = S ∧ registerMask K = S ∧
    ∀ m x y u v, |L m x y u v - K m x y u v| < ε

theorem register_fineConnected {ν : R → ℚ} {rev : M → M} {L K : Register M X R}
    {f : Setoid R} (hL : RegisterValid ν rev f L) (hK : RegisterValid ν rev f K)
    (h : registerMask L = registerMask K) {ε : ℚ} (hε : 0 < ε) :
    Relation.ReflTransGen (RegisterStep ν rev f (registerMask L) ε) L K := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  let N : ℕ := n+1
  have hnN : (n : ℚ) < (N : ℚ) := by exact_mod_cast Nat.lt_succ_self n
  have hN : 0 < (N : ℚ) := by exact_mod_cast Nat.succ_pos n
  let t (k : ℕ) := (k : ℚ) / (N : ℚ)
  have ht (k : ℕ) (hk : k ≤ N) : 0 ≤ t k ∧ t k ≤ 1 := by
    refine ⟨div_nonneg (by positivity) hN.le, (div_le_iff₀ hN).2 ?_⟩
    simpa using (show (k : ℚ) ≤ (N : ℚ) by exact_mod_cast hk)
  have hs (k : ℕ) (hk : k+1 ≤ N) :
      RegisterStep ν rev f (registerMask L) ε (registerMix L K (t k)) (registerMix L K (t (k+1))) := by
    have h₁ := ht k ((Nat.le_succ k).trans hk)
    have h₂ := ht (k+1) hk
    refine ⟨hL.mix hK h₁.1 h₁.2, hL.mix hK h₂.1 h₂.2,
      registerMix_mask hL hK h h₁.1 h₁.2, registerMix_mask hL hK h h₂.1 h₂.2, ?_⟩
    intro m x y u v
    have hdiff : registerMix L K (t k) m x y u v - registerMix L K (t (k+1)) m x y u v =
        (L m x y u v - K m x y u v) / (N : ℚ) := by
      simp only [registerMix, t, Nat.cast_add, Nat.cast_one]
      ring
    rw [hdiff, abs_div, abs_of_pos hN]
    apply (div_lt_iff₀ hN).2
    have habs : |L m x y u v - K m x y u v| ≤ 1 := by
      apply abs_le.mpr
      constructor
      · linarith [hL.1 m x y u v, hK.entry_le_one m x y u v]
      · linarith [hK.1 m x y u v, hL.entry_le_one m x y u v]
    exact habs.trans_lt (by
      have H : 1 < (N : ℚ) * ε := (div_lt_iff₀ hε).1 (hn.trans hnN)
      simpa [mul_comm] using H)
  have hchain (k : ℕ) (hk : k ≤ N) :
      Relation.ReflTransGen (RegisterStep ν rev f (registerMask L) ε)
        (registerMix L K (t 0)) (registerMix L K (t k)) := by
    induction k with
    | zero => exact .refl
    | succ k ih => exact (ih ((Nat.le_succ k).trans hk)).tail (hs k hk)
  have hstart : registerMix L K (t 0) = L := by funext m x y u v; simp [registerMix, t]
  have hfinal : registerMix L K (t N) = K := by funext m x y u v; simp [registerMix, t, hN.ne']
  simpa only [hstart, hfinal] using hchain N le_rfl

end MovingProjection
