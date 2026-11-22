import MovingProjection.NativeProbes

/-! Compilation of actual timed projected word experiments to exponent rows. -/

namespace MovingProjection

open scoped BigOperators

variable {I X M : Type*} [Fintype I] [Fintype X] [Fintype M] [DecidableEq I] [DecidableEq M]

def routeRateRow (u v : List M) : ExponentRow M :=
  ⟨fun m => u.count m, fun m => v.count m⟩

def characterExponent (w : List M) (i : I) (mi : M × I) : ℕ :=
  if mi.2 = i then w.count mi.1 else 0

def routeCharacterTest (u v : List M) (i : I) : MonomialTest (M × I) :=
  ⟨⟨characterExponent u i, characterExponent v i⟩, 1⟩

omit [Fintype I] [Fintype X] [DecidableEq I] in
theorem word_product_eq_monomial (w : List M) (f : M → ℚ) :
    (w.map f).prod = monomial (fun m => w.count m) f := by
  classical
  induction w with
  | nil => simp [monomial]
  | cons m w ih =>
    have hcount (a : M) : (m :: w).count a = w.count a + (if a = m then 1 else 0) := by
      by_cases h : a = m
      · subst a
        simp
      · simp [h, Ne.symm h]
    simp only [List.map_cons, List.prod_cons, ih, monomial, hcount, pow_add,
      Finset.prod_mul_distrib]
    have hf : (∏ a, f a ^ (if a = m then 1 else 0)) = f m := by
      simp
    rw [hf, mul_comm]

omit [Fintype X] in
theorem character_monomial (w : List M) (i : I) (a : M → I → ℚ) :
    monomial (characterExponent w i) (fun mi => a mi.1 mi.2) = (w.map (fun m => a m i)).prod := by
  rw [word_product_eq_monomial]
  unfold monomial
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro m _
  simp [characterExponent]

theorem route_character_compile (b : ParityBasis I X) [Nonempty X]
    (a : M → I → ℚ) (first next : M) (u v : List M) :
    b.nonemptyWord a first u = b.nonemptyWord a next v ↔
      ∀ i, (routeCharacterTest (first :: u) (next :: v) i).holds
        (fun mi => a mi.1 mi.2) := by
  rw [b.word_identity_iff]
  simp only [MonomialTest.holds, routeCharacterTest, one_mul, character_monomial]

omit [Fintype I] [Fintype X] [DecidableEq I] in
theorem route_rate_compile (u v : List M) (rate : M → ℚ) (c : ℚ) :
    (⟨routeRateRow u v, c⟩ : MonomialTest M).holds rate ↔
      (u.map rate).prod = c * (v.map rate).prod := by
  unfold MonomialTest.holds routeRateRow
  rw [word_product_eq_monomial, word_product_eq_monomial]

end MovingProjection
