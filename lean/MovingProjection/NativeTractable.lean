import MovingProjection.FiniteEventCompression

/-! At a fixed profile of a one-state instrument, either singleton words
or events of duration one give finely connected lawful rate fibers. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

variable {M : Type} [Fintype M] [DecidableEq M]
variable {held : (M → ℚ) → Prop} {floor : ℚ} {hf : 0 < floor}

private noncomputable def profilePoint (rate : M → ℚ) (h : RateLegal floor [] rate ∧ held rate) :
    ProfileState held floor hf :=
  ⟨toNative hf (tests := []) ⟨h.1.2.1, h.1.1, by simp⟩, rfl, h.2⟩

private theorem profile_legal (s : ProfileState held floor hf) :
    RateLegal floor [] s.1.law.rate ∧ held s.1.law.rate :=
  ⟨⟨s.1.legal.2.2.1.1, s.1.legal.2.2.1.2.1, by simp⟩, s.2.2⟩

private theorem profile_roundtrip (s : ProfileState held floor hf) :
    profilePoint s.1.law.rate (profile_legal s) = s := by
  let hs : EventState [] floor hf := ⟨s.1, s.2.1, by simp⟩
  have he := congrArg (fun u : EventState ([] : List (Test M)) floor hf => u.val)
    (lift_event_state_readback hs)
  exact Subtype.ext he

private theorem profile_chain_of_rate_chain {ε : ℚ} {s t : ProfileState held floor hf}
    (h : Relation.ReflTransGen (fun a b : M → ℚ =>
      (RateLegal floor [] a ∧ held a) ∧ (RateLegal floor [] b ∧ held b) ∧
        ∀ m, |a m - b m| < ε) s.1.law.rate t.1.law.rate) :
    Relation.ReflTransGen (ProfileStep ε) s t := by
  classical
  let p (a : M → ℚ) : ProfileState held floor hf :=
    if H : RateLegal floor [] a ∧ held a then profilePoint a H else s
  have hr (a : M → ℚ) (ha : RateLegal floor [] a ∧ held a) :
      (p a).1.law.rate = a := by simp [p, ha, profilePoint, toNative, law]
  have hone (a : ProfileState held floor hf) : p a.1.law.rate = a := by
    simp only [p, dif_pos (profile_legal a), profile_roundtrip]
  have he := h.lift p (fun a b hstep => by
    have H {s t : ProfileState held floor hf} :
        (∀ m, |s.1.law.rate m - t.1.law.rate m| < ε) → ProfileStep ε s t := by
      intro hnear
      let hs : EventState [] floor hf := ⟨s.1, s.2.1, by simp⟩
      let ht : EventState [] floor hf := ⟨t.1, t.2.1, by simp⟩
      exact (native_event_step_iff (a := hs) (b := ht) (ε := ε)).mpr
        ⟨event_state_rate_lawful hs, event_state_rate_lawful ht, hnear⟩
    apply H (s := p a) (t := p b)
    rw [hr a hstep.1, hr b hstep.2.1]
    exact hstep.2.2)
  simpa only [hone] using he

def linearTests (tests : List (Finset M × Finset M)) (rate : M → ℚ) : Prop :=
  ∀ t ∈ tests, (∑ m ∈ t.1, rate m) = (∑ m ∈ t.2, rate m)

theorem one_step_event_fine (tests : List (Finset M × Finset M))
    (s t : ProfileState (linearTests tests) floor hf) {ε : ℚ} (hε : 0 < ε) :
    Relation.ReflTransGen (ProfileStep ε) s t := by
  apply profile_chain_of_rate_chain
  let a := s.1.law.rate
  let b := t.1.law.rate
  have ha := profile_legal s
  have hb := profile_legal t
  let point (u : ℚ) (m : M) := (1-u) * a m + u * b m
  have hpoint (u : ℚ) (h₀ : 0 ≤ u) (h₁ : u ≤ 1) :
      RateLegal floor [] (point u) ∧ linearTests tests (point u) := by
    refine ⟨⟨fun m => ?_, ?_, by simp⟩, fun e he => ?_⟩
    · have hl := mul_le_mul_of_nonneg_left (ha.1.1 m) (sub_nonneg.mpr h₁)
      have hr := mul_le_mul_of_nonneg_left (hb.1.1 m) h₀
      change floor ≤ (1-u) * a m + u * b m
      change (1-u) * floor ≤ (1-u) * a m at hl
      change u * floor ≤ u * b m at hr
      nlinarith
    · have ha' : ∑ m, a m = 1 := ha.1.2.1
      have hb' : ∑ m, b m = 1 := hb.1.2.1
      simp only [point, Finset.sum_add_distrib, ← Finset.mul_sum, ha', hb']
      ring
    · have hl : ∑ m ∈ e.1, a m = ∑ m ∈ e.2, a m := ha.2 e he
      have hr : ∑ m ∈ e.1, b m = ∑ m ∈ e.2, b m := hb.2 e he
      simp only [point, Finset.sum_add_distrib, ← Finset.mul_sum, hl, hr]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hn₀ : (0 : ℚ) < n := (div_pos one_pos hε).trans hn
  have hsmall : 1 / (n : ℚ) < ε := by
    apply (div_lt_iff₀ hn₀).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn
  let sample (k : ℕ) := point ((k : ℚ) / n)
  have hlegal (k : ℕ) (hk : k ≤ n) :=
    hpoint ((k : ℚ) / n) (div_nonneg (Nat.cast_nonneg _) hn₀.le)
      ((div_le_one hn₀).mpr (by exact_mod_cast hk))
  let step (x y : M → ℚ) : Prop :=
    (RateLegal floor [] x ∧ linearTests tests x) ∧
      (RateLegal floor [] y ∧ linearTests tests y) ∧ ∀ m, |x m - y m| < ε
  have hmesh (k : ℕ) (hk : k ≤ n) : Relation.ReflTransGen step (sample 0) (sample k) := by
    induction k with
    | zero => exact .refl
    | succ k ih =>
      have hk' := (Nat.le_succ k).trans hk
      refine (ih hk').tail ⟨hlegal k hk', hlegal (k+1) hk, fun m => ?_⟩
      change |point ((k : ℚ) / n) m - point ((↑(k+1) : ℚ) / n) m| < ε
      rw [show point ((k : ℚ) / n) m - point ((↑(k+1) : ℚ) / n) m =
        (1 / (n : ℚ)) * (a m - b m) by simp only [point, Nat.cast_add, Nat.cast_one]; ring,
        abs_mul, abs_of_pos (div_pos one_pos hn₀)]
      have bound (x : M → ℚ) (hx : RateLegal floor [] x) : 0 ≤ x m ∧ x m ≤ 1 := by
        have hp (i : M) := hf.le.trans (hx.1 i)
        refine ⟨hp m, ?_⟩
        have hle := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ m)
        rwa [hx.2.1] at hle
      have hA := bound a ha.1
      have hB := bound b hb.1
      have hdiff : |a m - b m| ≤ 1 := abs_le.mpr
        ⟨by linarith [hA.1, hB.2], by linarith [hA.2, hB.1]⟩
      exact (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hdiff (div_nonneg zero_le_one hn₀.le) :
        (1 / (n : ℚ)) * |a m - b m| ≤ 1 / (n : ℚ)).trans_lt hsmall
  have hstart : sample 0 = a := by funext m; simp [sample, point]
  have hfinish : sample n = b := by funext m; simp [sample, point, hn₀.ne']
  have h := hmesh n le_rfl
  rw [hstart, hfinish] at h
  exact h

structure SingletonTest (M : Type) where
  left : List M
  right : List M
  ratio : ℚ
  ratio_pos : 0 < ratio
  duration : left.length = right.length

def singletonTests (tests : List (SingletonTest M)) (rate : M → ℚ) : Prop :=
  ∀ t ∈ tests, listMass rate t.left = t.ratio * listMass rate t.right

theorem singleton_event_fine [Nonempty M] (tests : List (SingletonTest M))
    (s t : ProfileState (singletonTests tests) floor hf) {ε : ℚ} (hε : 0 < ε) :
    Relation.ReflTransGen (ProfileStep ε) s t := by
  let encode (u : SingletonTest M) : MonomialTest M := ⟨routeRateRow u.left u.right, u.ratio⟩
  let monomials := tests.map encode
  have heq (x : M → ℚ) : RateLegal floor monomials x ↔
      RateLegal floor [] x ∧ singletonTests tests x := by
    have hmem (u : SingletonTest M) : (encode u).holds x ↔
        listMass x u.left = u.ratio * listMass x u.right :=
      route_rate_compile u.left u.right x u.ratio
    simp only [RateLegal, monomials, List.mem_map, List.not_mem_nil, false_implies, implies_true,
      and_true, singletonTests, ← and_assoc]
    apply and_congr_right
    intro _
    constructor
    · exact fun he u hu => (hmem u).mp (he _ ⟨u, hu, rfl⟩)
    · rintro hc _ ⟨u, hu, rfl⟩
      exact (hmem u).mpr (hc u hu)
  have hdegree (w : List M) : (∑ m, w.count m) = w.length := by
    rw [← List.sum_toFinset_count_eq_length]
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi =>
      List.count_eq_zero.mpr (fun h => hi (List.mem_toFinset.mpr h)))
  have hhom : ∀ u ∈ monomials, (∑ m, u.row.lhs m) = ∑ m, u.row.rhs m := by
    intro u hu
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
    change (∑ m, a.left.count m) = ∑ m, a.right.count m
    rw [hdegree, hdegree, a.duration]
  have hpos : ∀ u ∈ monomials, 0 < u.ratio := by
    intro u hu
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
    exact a.ratio_pos
  apply profile_chain_of_rate_chain
  have h := rate_fineConnected hf hhom hpos
    ((heq _).mpr (profile_legal s)) ((heq _).mpr (profile_legal t)) ε hε
  exact h.mono (fun _ _ hs => ⟨(heq _).mp hs.1, (heq _).mp hs.2.1, hs.2.2⟩)

end MovingProjection.OneStateEvents
