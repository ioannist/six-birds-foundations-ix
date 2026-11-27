import MovingProjection.NativeEvents
import MovingProjection.NativeWords
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-! Combine a catalogue of two-step event tests into one longer test. Each
term of the sum of squares gets its own balanced binary suffix, so the
result is a pair of finite events without repeated words. -/

namespace MovingProjection.OneStateEvents

open scoped BigOperators

variable {M : Type} [Fintype M] [decM : DecidableEq M]

def listMass (rate : M → ℚ) (word : List M) : ℚ := (word.map rate).prod

theorem native_list_mass {floor : ℚ} {hf : 0 < floor} (a : NativeState (M := M) floor hf)
    (word : List M) :
    nativeWordEndpoint (a.law.marked singletonParity) word ((), ()) () =
      listMass a.law.rate word := by
  have hlaw : a.law = law a.law.rate := by
    apply PhysicalLaw.ext
    · rfl
    · funext p
      exact p.2.elim
    · funext m x y u v
      have h := a.legal.2.2.2.2.1.2.1 m x y u
      simpa [law] using h
  have hm (m : M) (x y : Unit × Unit) : a.law.marked singletonParity m x y = a.law.rate m := by
    have hh := law_marked a.law.rate m x y
    exact hlaw.symm ▸ hh
  induction word with
  | nil => simp [nativeWordEndpoint, listMass]
  | cons m word ih =>
    simpa only [nativeWordEndpoint, listMass, List.map_cons, List.prod_cons, Fintype.sum_prod_type,
      Fintype.sum_unique, hm] using congrArg (fun u => a.law.rate m * u) ih

namespace FiniteEventCompression

omit [Fintype M] [DecidableEq M]

private def asList (w : Word M) : List M := [w.1, w.2]

private def terms : Test M → List (List M × Bool)
  | .equal l r => [(asList l, true), (asList r, false)]
  | .sum l r s _ => [(asList l, true), (asList r, false), (asList s, false)]

private def value (rate : M → ℚ) (t : List M × Bool) : ℚ :=
  if t.2 then listMass rate t.1 else -listMass rate t.1

private def termProduct (a b : List M × Bool) : List M × Bool :=
  (a.1 ++ b.1, a.2 == b.2)

private theorem value_product (rate : M → ℚ) (a b : List M × Bool) :
    value rate (termProduct a b) = value rate a * value rate b := by
  obtain ⟨a, c⟩ := a
  obtain ⟨b, d⟩ := b
  cases c <;> cases d <;> simp [value, termProduct, listMass]

private def square (t : Test M) : List (List M × Bool) :=
  (terms t).flatMap fun a => (terms t).map (termProduct a)

private def catalogue (tests : List (Test M)) : List (List M × Bool) := tests.flatMap square

private theorem square_has_sign (t : Test M) (sign : Bool) :
    ∃ w ∈ square t, w.2 = sign := by
  have hone : ∃ u ∈ terms t, u.2 = true := by
    cases t <;> simp [terms]
  have hneg : ∃ v ∈ terms t, v.2 = false := by
    cases t <;> simp [terms]
  obtain ⟨u, hu, hupos⟩ := hone
  obtain ⟨v, hv, hvs⟩ := hneg
  let w := if sign then u else v
  have hw : w ∈ terms t := by
    cases sign
    · simpa [w] using hv
    · simpa [w] using hu
  have hs : w.2 = sign := by cases sign <;> simp [w, hupos, hvs]
  refine ⟨termProduct u w, List.mem_flatMap.mpr ⟨u, hu, List.mem_map_of_mem hw⟩, ?_⟩
  cases sign <;> simp [termProduct, hupos, hs]

private theorem value_terms (rate : M → ℚ) (t : Test M) :
    ((terms t).map (value rate)).sum = 0 ↔ t.holds rate := by
  cases t <;> simp [terms, asList, value, listMass, Test.holds, wordMass] <;>
    constructor <;> intro h <;> linarith

private theorem sum_list_mul {A : Type} (l : List A) (f : A → ℚ) (c : ℚ) :
    (l.map (fun a => c * f a)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

private theorem value_square (rate : M → ℚ) (t : Test M) :
    ((square t).map (value rate)).sum = (((terms t).map (value rate)).sum)^2 := by
  have h (l r : List (List M × Bool)) :
      (((l.flatMap fun a => r.map (termProduct a)).map (value rate))).sum =
        (l.map (value rate)).sum * (r.map (value rate)).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map, List.map_cons,
        List.sum_cons, ih, add_mul]
      change (r.map (fun b => value rate (termProduct a b))).sum + _ = _
      simp only [value_product, sum_list_mul]
  rw [square, h, pow_two]

private theorem term_length (tests : List (Test M)) (t : List M × Bool)
    (ht : t ∈ catalogue tests) : t.1.length = 4 := by
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp ht
  obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hab
  have hl (e : List M × Bool) (he : e ∈ terms c) : e.1.length = 2 := by
    cases c <;> simp [terms, asList] at he <;> aesop
  simp [termProduct, hl a ha, hl b hb]

private theorem catalogue_length (tests : List (Test M)) : (catalogue tests).length ≤ 9 * tests.length := by
  induction tests with
  | nil => simp [catalogue]
  | cons t ts ih =>
    have ht : (square t).length ≤ 9 := by cases t <;> simp [square, terms]
    simp only [catalogue, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

private theorem catalogue_zero_iff (tests : List (Test M)) (rate : M → ℚ) :
    ((catalogue tests).map (value rate)).sum = 0 ↔ ∀ t ∈ tests, t.holds rate := by
  have hnonneg (l : List (Test M)) : 0 ≤ ((catalogue l).map (value rate)).sum := by
    induction l with
    | nil => simp [catalogue]
    | cons t ts ih =>
      change 0 ≤ ((square t ++ catalogue ts).map (value rate)).sum
      rw [List.map_append, List.sum_append, value_square]
      exact add_nonneg (sq_nonneg _) ih
  induction tests with
  | nil => simp [catalogue]
  | cons t ts ih =>
    change ((square t ++ catalogue ts).map (value rate)).sum = 0 ↔ _
    rw [List.map_append, List.sum_append, value_square,
      add_eq_zero_iff_of_nonneg (sq_nonneg _) (hnonneg ts)]
    simp only [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), value_terms, ih, List.forall_mem_cons]

private def suffix (a b : M) : List Bool → List M
  | [] => []
  | c :: cs => (if c then [a,b] else [b,a]) ++ suffix a b cs

private theorem suffix_length (a b : M) (bits : List Bool) :
    (suffix a b bits).length = 2 * bits.length := by
  induction bits with
  | nil => simp [suffix]
  | cons c cs ih => cases c <;> simp [suffix, ih] <;> omega

private theorem suffix_injective (a b : M) (hab : a ≠ b) : Function.Injective (suffix a b) := by
  intro x
  induction x with
  | nil =>
    intro y h
    cases y with
    | nil => rfl
    | cons c cs => cases c <;> simp [suffix] at h
  | cons c cs ih =>
    intro y h
    cases y with
    | nil => cases c <;> simp [suffix] at h
    | cons d ds =>
      cases c <;> cases d <;> simp [suffix, hab, hab.symm] at h ⊢
      all_goals exact ih h

private theorem suffix_mass (a b : M) (bits : List Bool) (rate : M → ℚ) :
    listMass rate (suffix a b bits) = (rate a * rate b) ^ bits.length := by
  induction bits with
  | nil => simp [suffix, listMass]
  | cons c cs ih =>
    cases c <;> simp [suffix, listMass, listMass] at ih ⊢ <;>
      rw [ih, pow_succ] <;> ring

variable (tests : List (Test M))

def suffixPairs : ℕ := Nat.clog 2 (max 2 (catalogue tests).length)

def bits (i : Fin (catalogue tests).length) : List Bool :=
  List.ofFn fun k : Fin (suffixPairs tests) => i.val.testBit k.val

theorem bits_injective : Function.Injective (bits tests) := by
  intro i j h
  have he := List.ofFn_injective h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < suffixPairs tests
  · exact congrFun he ⟨k, hk⟩
  · have hle : (catalogue tests).length ≤ 2 ^ suffixPairs tests :=
      (le_max_right 2 _).trans (Nat.le_pow_clog (by decide) _)
    have hp : 2 ^ suffixPairs tests ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (le_of_not_gt hk)
    rw [Nat.testBit_lt_two_pow (i.isLt.trans_le (hle.trans hp)),
      Nat.testBit_lt_two_pow (j.isLt.trans_le (hle.trans hp))]

theorem bits_length (i : Fin (catalogue tests).length) : (bits tests i).length = suffixPairs tests := by
  simp [bits]

def outputWord (a b : M) (i : Fin (catalogue tests).length) : List M :=
  ((catalogue tests).get i).1 ++ suffix a b (bits tests i)

theorem outputWord_length (a b : M) (i : Fin (catalogue tests).length) :
    (outputWord tests a b i).length = 4 + 2 * suffixPairs tests := by
  simp only [outputWord, List.length_append, suffix_length, bits_length]
  rw [term_length _ _ (List.get_mem _ i)]

theorem outputWord_injective (a b : M) (hab : a ≠ b) : Function.Injective (outputWord tests a b) := by
  intro i j h
  have h' := congrArg (List.drop 4) h
  have hdrop (k : Fin (catalogue tests).length) :
      (outputWord tests a b k).drop 4 = suffix a b (bits tests k) := by
    unfold outputWord
    rw [← term_length tests ((catalogue tests).get k) (List.get_mem _ k)]
    simp
  rw [hdrop, hdrop] at h'
  exact bits_injective tests (suffix_injective a b hab h')

include decM

def event (a b : M) (sign : Bool) : Finset (List M) :=
  (Finset.univ.filter fun i => ((catalogue tests).get i).2 = sign).image (outputWord tests a b)

theorem event_word_length (a b : M) (sign : Bool) {word : List M}
    (hw : word ∈ event tests a b sign) : word.length = 4 + 2 * suffixPairs tests := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
  exact outputWord_length tests a b i

theorem event_nonempty (a b : M) (sign : Bool) (ht : tests ≠ []) :
    (event tests a b sign).Nonempty := by
  obtain ⟨test, htest⟩ := List.exists_mem_of_ne_nil tests ht
  obtain ⟨w, hw, hs⟩ := square_has_sign test sign
  have hm : w ∈ catalogue tests := List.mem_flatMap.mpr ⟨test, htest, hw⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  refine ⟨outputWord tests a b i, Finset.mem_image.mpr ⟨i, ?_, rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by rw [hi, hs]⟩

theorem event_mass_pos (a b : M) (sign : Bool) (ht : tests ≠ []) (rate : M → ℚ)
    (hr : ∀ m, 0 < rate m) :
    0 < ∑ w ∈ event tests a b sign, listMass rate w :=
  Finset.sum_pos (fun w _ => by
    unfold listMass
    exact List.prod_pos (fun z hz => by obtain ⟨m, _, rfl⟩ := List.mem_map.mp hz; exact hr m))
    (event_nonempty tests a b sign ht)

theorem event_card_add_le (a b : M) :
    (event tests a b true).card + (event tests a b false).card ≤ 9 * tests.length := by
  unfold event
  apply le_trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have hp : (Finset.univ.filter fun i => ((catalogue tests).get i).2 = false) =
      (Finset.univ.filter fun i => ¬ ((catalogue tests).get i).2 = true) := by
    apply Finset.filter_congr
    intro i _
    cases ((catalogue tests).get i).2 <;> simp
  rw [hp, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  exact catalogue_length tests

theorem event_probability_iff (a b : M) (hab : a ≠ b) (rate : M → ℚ)
    (ha : 0 < rate a) (hb : 0 < rate b) :
    (∑ w ∈ event tests a b true, listMass rate w) =
      (∑ w ∈ event tests a b false, listMass rate w) ↔ ∀ t ∈ tests, t.holds rate := by
  rw [← catalogue_zero_iff]
  have hmass (i : Fin (catalogue tests).length) :
      listMass rate (outputWord tests a b i) =
        listMass rate ((catalogue tests).get i).1 * (rate a * rate b)^suffixPairs tests := by
    unfold outputWord
    rw [show listMass rate (((catalogue tests).get i).1 ++ suffix a b (bits tests i)) =
      listMass rate ((catalogue tests).get i).1 * listMass rate (suffix a b (bits tests i)) by
        simp [listMass], suffix_mass, bits_length]
  rw [← sub_eq_zero]
  simp only [event, Finset.sum_image (fun _ _ _ _ h => outputWord_injective tests a b hab h),
    hmass, Finset.sum_filter, ← Finset.sum_sub_distrib]
  have hdiff (i : Fin (catalogue tests).length) :
      ((if ((catalogue tests).get i).2 = true then
        listMass rate ((catalogue tests).get i).1 * (rate a * rate b) ^ suffixPairs tests else 0) -
      (if ((catalogue tests).get i).2 = false then
        listMass rate ((catalogue tests).get i).1 * (rate a * rate b) ^ suffixPairs tests else 0)) =
      value rate ((catalogue tests).get i) * (rate a * rate b) ^ suffixPairs tests := by
    unfold value
    cases ((catalogue tests).get i).2 <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, sub_zero,
        zero_sub, neg_mul]
  simp only [hdiff, ← Finset.sum_mul, mul_eq_zero, pow_ne_zero _ (mul_ne_zero ha.ne' hb.ne'),
    or_false]
  rw [← List.sum_ofFn]
  have he := congrArg (fun l => l.map (value rate)) (List.ofFn_get (catalogue tests))
  simp only [List.map_ofFn] at he
  change List.ofFn (fun i => value rate ((catalogue tests).get i)) = _ at he
  rw [he]

abbrev CompressedState [Fintype M] (a b : M) (floor : ℚ) (hf : 0 < floor) :=
  ProfileState (fun rate => (∑ w ∈ event tests a b true, listMass rate w) =
    (∑ w ∈ event tests a b false, listMass rate w)) floor hf

variable [Fintype M]

theorem measured_event_pos (a b : M) (sign : Bool) (ht : tests ≠ [])
    {floor : ℚ} {hf : 0 < floor} (s : NativeState (M := M) floor hf) :
    0 < ∑ w ∈ event tests a b sign, nativeWordEndpoint
      (s.law.marked singletonParity) w ((), ()) () := by
  simp only [native_list_mass]
  exact event_mass_pos tests a b sign ht s.law.rate (fun m => hf.trans_le (s.legal.2.2.1.1 m))

theorem measured_test_iff (a b : M) {floor : ℚ} {hf : 0 < floor}
    (s : NativeState (M := M) floor hf) :
    ((∑ w ∈ event tests a b true, nativeWordEndpoint (s.law.marked singletonParity) w ((), ()) ()) =
      (∑ w ∈ event tests a b false, nativeWordEndpoint (s.law.marked singletonParity) w ((), ()) ())) ↔
    (∑ w ∈ event tests a b true, listMass s.law.rate w) =
      (∑ w ∈ event tests a b false, listMass s.law.rate w) := by
  simp only [native_list_mass]

noncomputable def compress (a b : M) (hab : a ≠ b) {floor : ℚ} {hf : 0 < floor}
    (s : EventState tests floor hf) : CompressedState tests a b floor hf :=
  ⟨s.1, s.2.1,
    (event_probability_iff tests a b hab _ (hf.trans_le (s.1.legal.2.2.1.1 a))
      (hf.trans_le (s.1.legal.2.2.1.1 b))).mpr s.2.2⟩

private noncomputable def expand (a b : M) (hab : a ≠ b) {floor : ℚ} {hf : 0 < floor}
    (s : CompressedState tests a b floor hf) : EventState tests floor hf :=
  ⟨s.1, s.2.1,
    (event_probability_iff tests a b hab _ (hf.trans_le (s.1.legal.2.2.1.1 a))
      (hf.trans_le (s.1.legal.2.2.1.1 b))).mp s.2.2⟩

/-- The two fixed-profile predicates describe the same rate vectors. -/
noncomputable def compressedEquiv (a b : M) (hab : a ≠ b) {floor : ℚ} {hf : 0 < floor} :
    EventState tests floor hf ≃ CompressedState tests a b floor hf where
  toFun := compress tests a b hab
  invFun := expand tests a b hab
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem compressedEquiv_rate (a b : M) (hab : a ≠ b) {floor : ℚ} {hf : 0 < floor}
    (s : EventState tests floor hf) :
    ((compressedEquiv tests a b hab) s).val.law.rate = s.val.law.rate :=
  rfl

theorem compressed_step_iff (a b : M) (hab : a ≠ b) {floor ε : ℚ} {hf : 0 < floor}
    (s t : EventState tests floor hf) :
    ProfileStep ε (compressedEquiv tests a b hab s) (compressedEquiv tests a b hab t) ↔
      NativeEventStep ε s t :=
  Iff.rfl

theorem compressed_chain_iff (a b : M) (hab : a ≠ b) {floor ε : ℚ} {hf : 0 < floor}
    (s t : EventState tests floor hf) :
    Relation.ReflTransGen (ProfileStep ε) (compress tests a b hab s) (compress tests a b hab t) ↔
      Relation.ReflTransGen (NativeEventStep ε) s t := by
  constructor
  · intro h
    have he (r : EventState tests floor hf) : expand tests a b hab (compress tests a b hab r) = r :=
      (compressedEquiv tests a b hab).left_inv r
    have hh := h.lift (expand tests a b hab) (fun p q (hstep : ProfileStep ε p q) =>
      show NativeEventStep ε (expand tests a b hab p) (expand tests a b hab q) from hstep)
    simpa only [he] using hh
  · intro h
    exact h.lift (compress tests a b hab) (fun p q (hstep : NativeEventStep ε p q) =>
      show ProfileStep ε (compress tests a b hab p) (compress tests a b hab q) from hstep)

end FiniteEventCompression

end MovingProjection.OneStateEvents
