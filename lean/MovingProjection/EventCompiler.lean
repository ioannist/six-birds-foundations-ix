import MovingProjection.RateExpressions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A uniform compiler from positive equations to two-step event tests.
Auxiliary rates are uniquely determined at every real or rational point of
the unit box. Two copies of each value allow addition of equal expressions
using two distinct words. Each copy has its own complementary rate. -/

namespace MovingProjection.OneStateEvents.Equations

open scoped BigOperators

variable {I : Type} [DecidableEq I]

def power (eqs : Equations I) : ℕ := max 2 (Nat.clog 2 (eqs.nodes.sup Expr.bound + 1))

def capacity (eqs : Equations I) : ℚ := 2 ^ eqs.power

theorem power_ge_two (eqs : Equations I) : 2 ≤ eqs.power := le_max_left _ _

abbrev Node (eqs : Equations I) := ↥eqs.nodes

abbrev Mark (eqs : Equations I) :=
  (Fin (eqs.power + 1) × Bool) ⊕ ((I × Bool) ⊕ (eqs.Node × Bool × Bool))

def ref (eqs : Equations I) (j : Fin (eqs.power + 1)) (copy : Bool) : eqs.Mark :=
  .inl (j, copy)

def box (eqs : Equations I) (i : I) (complement : Bool) : eqs.Mark :=
  .inr (.inl (i, complement))

def aux (eqs : Equations I) (e : eqs.Node) (copy complement : Bool) : eqs.Mark :=
  .inr (.inr (e, copy, complement))

def root (eqs : Equations I) : eqs.Mark := eqs.ref 0 false

def refFour (eqs : Equations I) : eqs.Mark :=
  eqs.ref ⟨2, Nat.lt_succ_of_le eqs.power_ge_two⟩ false

def refCap (eqs : Equations I) : eqs.Mark := eqs.ref (Fin.last eqs.power) false

theorem capacity_ge_bound (eqs : Equations I) (e : eqs.Node) :
    (e.val.bound : ℚ) + 1 ≤ eqs.capacity := by
  have hbase : e.val.bound + 1 ≤ eqs.nodes.sup Expr.bound + 1 :=
    Nat.succ_le_succ (Finset.le_sup (f := Expr.bound) e.property)
  have h : e.val.bound + 1 ≤ 2 ^ eqs.power := by
    apply hbase.trans ((Nat.le_pow_clog (by decide : 1 < 2) _).trans ?_)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right 2 _)
  unfold capacity
  exact_mod_cast h

def equalRate (eqs : Equations I) (a b : eqs.Mark) : Test eqs.Mark :=
  .equal (a, eqs.root) (b, eqs.root)

def sumRate (eqs : Equations I) (z a b : eqs.Mark) (hne : a ≠ b) : Test eqs.Mark :=
  .sum (z, eqs.root) (a, eqs.root) (b, eqs.root) (fun h => hne (congrArg Prod.fst h))

def productRate (eqs : Equations I) (z a b : eqs.Mark) : Test eqs.Mark :=
  .equal (z, eqs.root) (a, b)

theorem equalRate_iff {eqs : Equations I} {rate : eqs.Mark → ℚ}
    {a b : eqs.Mark} (hr : rate eqs.root ≠ 0) :
    (eqs.equalRate a b).holds rate ↔ rate a = rate b :=
  mul_left_inj' hr

theorem sumRate_iff {eqs : Equations I} {rate : eqs.Mark → ℚ}
    {z a b : eqs.Mark} {hne : a ≠ b} (hr : rate eqs.root ≠ 0) :
    (eqs.sumRate z a b hne).holds rate ↔ rate z = rate a + rate b :=
  padded_add_iff hne hr

theorem productRate_iff {eqs : Equations I} {rate : eqs.Mark → ℚ}
    {z a b : eqs.Mark} (hr : rate eqs.root ≠ 0) :
    (eqs.productRate z a b).holds rate ↔ rate z = rate a * rate b / rate eqs.root :=
  product_iff hr

private def doubleTest (eqs : Equations I) (j : Fin eqs.power) : Test eqs.Mark :=
  eqs.sumRate (eqs.ref j.succ false) (eqs.ref j.castSucc false) (eqs.ref j.castSucc true)
    (by simp [ref])

private def boxPairTest (eqs : Equations I) (i : I) : Test eqs.Mark :=
  eqs.sumRate eqs.refFour (eqs.box i false) (eqs.box i true) (by simp [box])

private def auxPairTest (eqs : Equations I) (e : eqs.Node) (copy : Bool) : Test eqs.Mark :=
  eqs.sumRate eqs.refCap (eqs.aux e copy false) (eqs.aux e copy true) (by simp [aux])

private def nodeTest (eqs : Equations I) : eqs.Node → Test eqs.Mark
  | ⟨.one, he⟩ => eqs.equalRate (eqs.aux ⟨.one, he⟩ false false) eqs.root
  | ⟨.coordinate i b, he⟩ =>
    eqs.equalRate (eqs.aux ⟨.coordinate i b, he⟩ false false) (eqs.box i b)
  | ⟨.add a b, he⟩ =>
    let av : eqs.Node := ⟨a, subexpression_mem he (by
      simp [Expr.subexpressions, a.self_mem_subexpressions])⟩
    let bv : eqs.Node := ⟨b, subexpression_mem he (by
      simp [Expr.subexpressions, b.self_mem_subexpressions])⟩
    eqs.sumRate (eqs.aux ⟨.add a b, he⟩ false false) (eqs.aux av false false)
      (eqs.aux bv true false) (by simp [aux])
  | ⟨.mul a b, he⟩ =>
    let av : eqs.Node := ⟨a, subexpression_mem he (by
      simp [Expr.subexpressions, a.self_mem_subexpressions])⟩
    let bv : eqs.Node := ⟨b, subexpression_mem he (by
      simp [Expr.subexpressions, b.self_mem_subexpressions])⟩
    eqs.productRate (eqs.aux ⟨.mul a b, he⟩ false false) (eqs.aux av false false)
      (eqs.aux bv false false)

private def equationTest (eqs : Equations I) (e : {e // e ∈ eqs}) : Test eqs.Mark :=
  eqs.equalRate (eqs.aux ⟨e.val.1, eqs.left_mem e.property⟩ false false)
    (eqs.aux ⟨e.val.2, eqs.right_mem e.property⟩ false false)

variable [Fintype I]

private noncomputable def allTests {α β : Type} [Fintype α] (f : α → β) : List β :=
  Finset.univ.toList.map f

@[simp] private theorem forall_allTests {α β : Type} [Fintype α] (f : α → β) (P : β → Prop) :
    (∀ a ∈ allTests f, P a) ↔ ∀ a, P (f a) := by
  simp [allTests]

noncomputable def tests (eqs : Equations I) : List (Test eqs.Mark) :=
  allTests (fun j => eqs.equalRate (eqs.ref j true) (eqs.ref j false)) ++
  allTests eqs.doubleTest ++ allTests eqs.boxPairTest ++
  allTests (fun a : eqs.Node × Bool => eqs.auxPairTest a.1 a.2) ++
  allTests (fun e => eqs.equalRate (eqs.aux e true false) (eqs.aux e false false)) ++
  allTests eqs.nodeTest ++ eqs.attach.map eqs.equationTest

theorem mark_card (eqs : Equations I) :
    Fintype.card eqs.Mark = 2 * (eqs.power + 1) + 2 * Fintype.card I + 4 * eqs.nodes.card := by
  simp [Mark, Node]
  omega

theorem tests_length (eqs : Equations I) :
    eqs.tests.length = 2 * eqs.power + 1 + Fintype.card I + 4 * eqs.nodes.card + eqs.length := by
  simp [tests, allTests, Node]
  omega

theorem tests_ne_nil (eqs : Equations I) : eqs.tests ≠ [] := by
  intro h
  have hl := eqs.tests_length
  rw [h, List.length_nil] at hl
  omega

private structure HoldsTests (eqs : Equations I) (rate : eqs.Mark → ℚ) : Prop where
  refCopy : ∀ j, (eqs.equalRate (eqs.ref j true) (eqs.ref j false)).holds rate
  refDouble : ∀ j, (eqs.doubleTest j).holds rate
  inputs : ∀ i, (eqs.boxPairTest i).holds rate
  outputs : ∀ e b, (eqs.auxPairTest e b).holds rate
  auxCopy : ∀ e, (eqs.equalRate (eqs.aux e true false) (eqs.aux e false false)).holds rate
  nodes : ∀ e, (eqs.nodeTest e).holds rate
  equations : ∀ e : {e // e ∈ eqs}, (eqs.equationTest e).holds rate

private theorem holdsTests_iff (eqs : Equations I) (rate : eqs.Mark → ℚ) :
    (∀ test ∈ eqs.tests, test.holds rate) ↔ HoldsTests eqs rate := by
  simp only [tests, List.forall_mem_append, forall_allTests, Prod.forall,
    List.forall_mem_map, List.mem_attach, true_implies, and_assoc]
  constructor
  · rintro ⟨a, b, c, d, e, f, g⟩
    exact ⟨a, b, c, d, e, f, g⟩
  · rintro ⟨a, b, c, d, e, f, g⟩
    exact ⟨a, b, c, d, e, f, g⟩

def total (eqs : Equations I) : ℚ :=
  (∑ j : Fin (eqs.power + 1), 2 * (2 : ℚ) ^ (j : ℕ)) +
    (∑ _ : I, (4 : ℚ)) + ∑ _ : eqs.Node, ∑ _ : Bool, eqs.capacity

theorem total_pos (eqs : Equations I) : 0 < eqs.total := by
  unfold total
  have h := Finset.single_le_sum
    (fun (j : Fin (eqs.power + 1)) (_ : j ∈ Finset.univ) =>
      show 0 ≤ (2 : ℚ) * 2 ^ (j : ℕ) by positivity)
    (Finset.mem_univ (0 : Fin (eqs.power + 1)))
  have href : 0 < (∑ j : Fin (eqs.power + 1), 2 * (2 : ℚ) ^ (j : ℕ)) :=
    (by positivity : 0 < (2 : ℚ) * 2 ^ ((0 : Fin (eqs.power + 1)) : ℕ)).trans_le h
  have hb : 0 ≤ (∑ _ : I, (4 : ℚ)) := Finset.sum_nonneg (fun _ _ => by norm_num)
  have ha : 0 ≤ (∑ _ : eqs.Node, ∑ _ : Bool, eqs.capacity) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by unfold capacity; positivity
  linarith

def floor (eqs : Equations I) : ℚ := 1 / eqs.total

theorem floor_pos (eqs : Equations I) : 0 < eqs.floor := div_pos one_pos eqs.total_pos

theorem floor_mul_total (eqs : Equations I) : eqs.floor * eqs.total = 1 :=
  (div_mul_cancel₀ _ eqs.total_pos.ne')

private theorem sum_of_pairs (eqs : Equations I) (rate : eqs.Mark → ℚ) (r : ℚ)
    (href : ∀ j b, rate (eqs.ref j b) = r * 2 ^ (j : ℕ))
    (hbox : ∀ i, rate (eqs.box i true) + rate (eqs.box i false) = r * 4)
    (haux : ∀ e b, rate (eqs.aux e b true) + rate (eqs.aux e b false) = r * eqs.capacity) :
    (∑ m, rate m) = r * eqs.total := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
  change (∑ j, (rate (eqs.ref j true) + rate (eqs.ref j false))) +
    ((∑ i, (rate (eqs.box i true) + rate (eqs.box i false))) +
    ∑ e, ((rate (eqs.aux e true true) + rate (eqs.aux e true false)) +
      (rate (eqs.aux e false true) + rate (eqs.aux e false false)))) = r * eqs.total
  simp only [href, hbox, haux, total, mul_add, Finset.mul_sum, Fintype.sum_bool]
  have h : (∑ j : Fin (eqs.power + 1), (r * 2 ^ (j : ℕ) + r * 2 ^ (j : ℕ))) =
      ∑ j : Fin (eqs.power + 1), r * (2 * 2 ^ (j : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

omit [Fintype I] in
private theorem ref_values (eqs : Equations I) (rate : eqs.Mark → ℚ)
    (h : HoldsTests eqs rate) (hr : rate eqs.root ≠ 0) :
    ∀ j b, rate (eqs.ref j b) = rate eqs.root * 2 ^ (j : ℕ) := by
  have copy (j : Fin (eqs.power + 1)) := equalRate_iff hr |>.mp (h.refCopy j)
  have value (j : Fin (eqs.power + 1)) : rate (eqs.ref j false) = rate eqs.root * 2 ^ (j : ℕ) := by
    induction j using Fin.induction with
    | zero => simp [root]
    | succ j ih =>
      have hd := (sumRate_iff hr).mp (h.refDouble j)
      rw [hd, copy j.castSucc, ih]
      change _ = rate eqs.root * 2 ^ ((j : ℕ) + 1)
      rw [Fin.val_castSucc, pow_succ]
      ring
  intro j b
  cases b
  · exact value j
  · rw [copy j, value j]

def decode (eqs : Equations I) : (eqs.Mark → ℚ) → I → ℚ :=
  readCube (fun i => eqs.box i false) eqs.floor

def encode (eqs : Equations I) (x : I → ℚ) : eqs.Mark → ℚ
  | .inl (j, _) => eqs.floor * 2 ^ (j : ℕ)
  | .inr (.inl (i, b)) => eqs.floor * unitRate x i b
  | .inr (.inr (e, _, false)) => eqs.floor * e.val.eval x
  | .inr (.inr (e, _, true)) => eqs.floor * (eqs.capacity - e.val.eval x)

@[simp] theorem encode_ref (eqs : Equations I) (x : I → ℚ) (j : Fin (eqs.power + 1)) (b : Bool) :
    eqs.encode x (eqs.ref j b) = eqs.floor * 2 ^ (j : ℕ) := rfl

@[simp] theorem encode_root (eqs : Equations I) (x : I → ℚ) :
    eqs.encode x eqs.root = eqs.floor := by simp [root]

@[simp] theorem encode_box (eqs : Equations I) (x : I → ℚ) (i : I) (b : Bool) :
    eqs.encode x (eqs.box i b) = eqs.floor * unitRate x i b := rfl

@[simp] theorem encode_aux (eqs : Equations I) (x : I → ℚ) (e : eqs.Node) (b : Bool) :
    eqs.encode x (eqs.aux e b false) = eqs.floor * e.val.eval x := rfl

@[simp] theorem encode_complement (eqs : Equations I) (x : I → ℚ) (e : eqs.Node) (b : Bool) :
    eqs.encode x (eqs.aux e b true) = eqs.floor * (eqs.capacity - e.val.eval x) := rfl

@[simp] theorem decode_encode (eqs : Equations I) (x : I → ℚ) : eqs.decode (eqs.encode x) = x := by
  funext i
  simp [decode, readCube, unitRate, eqs.floor_pos.ne']

theorem encode_lawful (eqs : Equations I) {x : I → ℚ} (hx : InBox x) (he : eqs.holds x) :
    Lawful eqs.tests eqs.floor (eqs.encode x) := by
  have hr := eqs.floor_pos
  have hne : eqs.encode x eqs.root ≠ 0 := by simp [hr.ne']
  refine ⟨?_, ?_, (holdsTests_iff _ _).mpr ?_⟩
  · rw [eqs.sum_of_pairs (eqs.encode x) eqs.floor (eqs.encode_ref x), eqs.floor_mul_total]
    · intro i
      rw [encode_box, encode_box, ← mul_add, add_comm (unitRate x i true), unitRate_pair]
    · intro e b
      rw [encode_complement, encode_aux, ← mul_add]
      ring
  · intro m
    have hb : ∀ b : ℚ, 1 ≤ b → eqs.floor ≤ eqs.floor * b := fun _ h => by
      simpa using mul_le_mul_of_nonneg_left h hr.le
    rcases m with ⟨j, b⟩ | ⟨i, b⟩ | ⟨e, copy, b⟩
    · exact hb _ (one_le_pow₀ (by norm_num))
    · exact hb _ (unitRate_bounds hx i b).1
    · cases b
      · exact hb _ (e.val.eval_bounds hx).1
      · apply hb
        have hcap := eqs.capacity_ge_bound e
        have hev := (e.val.eval_bounds hx).2
        change 1 ≤ eqs.capacity - e.val.eval x
        linarith
  · constructor
    · intro j
      exact (equalRate_iff hne).mpr (by simp)
    · intro j
      apply (sumRate_iff hne).mpr
      simp only [encode_ref, Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring
    · intro i
      apply (sumRate_iff hne).mpr
      simp only [refFour, encode_ref, encode_box, ← mul_add, unitRate_pair]
      rfl
    · intro e b
      apply (sumRate_iff hne).mpr
      simp only [refCap, encode_ref, encode_aux, encode_complement, Fin.val_last, capacity]
      ring
    · intro e
      exact (equalRate_iff hne).mpr (by simp)
    · rintro ⟨e, hm⟩
      cases e with
      | one => exact (equalRate_iff hne).mpr (by simp [Expr.eval])
      | coordinate i b => exact (equalRate_iff hne).mpr (by simp [Expr.eval])
      | add a b =>
        apply (sumRate_iff hne).mpr
        · simp [Expr.eval, mul_add]
        · simp [aux]
      | mul a b =>
        apply (productRate_iff hne).mpr
        simp only [encode_aux, encode_root, Expr.eval]
        field_simp
    · intro e
      exact (equalRate_iff hne).mpr (by simp [he e.val e.property])

theorem lawful_decode (eqs : Equations I) {rate : eqs.Mark → ℚ}
    (h : Lawful eqs.tests eqs.floor rate) :
    InBox (eqs.decode rate) ∧ eqs.holds (eqs.decode rate) ∧ eqs.encode (eqs.decode rate) = rate := by
  let x := eqs.decode rate
  have hc := (holdsTests_iff _ _).mp h.2.2
  have hrootPos : 0 < rate eqs.root := eqs.floor_pos.trans_le (h.2.1 _)
  have hrr := eqs.ref_values rate hc hrootPos.ne'
  have hf : rate eqs.refFour = rate eqs.root * 4 := by simpa [refFour] using hrr ⟨2, _⟩ false
  have hp : rate eqs.refCap = rate eqs.root * eqs.capacity := by
    simpa [refCap, capacity] using hrr (Fin.last eqs.power) false
  have hbox (i : I) : rate (eqs.box i true) + rate (eqs.box i false) = rate eqs.root * 4 := by
    have he := (sumRate_iff hrootPos.ne').mp (hc.inputs i)
    linarith
  have haux (e : eqs.Node) (b : Bool) :
      rate (eqs.aux e b true) + rate (eqs.aux e b false) = rate eqs.root * eqs.capacity := by
    have he := (sumRate_iff hrootPos.ne').mp (hc.outputs e b)
    linarith
  have hroot : rate eqs.root = eqs.floor := by
    apply (eq_div_iff eqs.total_pos.ne').mpr
    rw [← eqs.sum_of_pairs rate (rate eqs.root) hrr hbox haux, h.1]
  have hdup (e : eqs.Node) := (equalRate_iff hrootPos.ne').mp (hc.auxCopy e)
  have hbox' (i : I) (b : Bool) : rate (eqs.box i b) = eqs.floor * unitRate x i b := by
    have hf' : rate (eqs.box i false) = eqs.floor * unitRate x i false := by
      change rate (eqs.box i false) = eqs.floor * (1 + 2 * ((rate (eqs.box i false) / eqs.floor - 1) / 2))
      rw [show 1 + 2 * ((rate (eqs.box i false) / eqs.floor - 1) / 2) =
        rate (eqs.box i false) / eqs.floor by ring, mul_comm eqs.floor]
      exact (div_mul_cancel₀ _ eqs.floor_pos.ne').symm
    cases b
    · exact hf'
    · have hs := hbox i
      rw [hroot, hf'] at hs
      rw [show unitRate x i true = 4 - unitRate x i false by linarith [unitRate_pair x i], mul_sub]
      linarith
  have hboxIn : InBox x := by
    intro i
    have hleft := h.2.1 (eqs.box i false)
    have hright := h.2.1 (eqs.box i true)
    rw [hbox' i false] at hleft
    rw [hbox' i true] at hright
    have strip (v : ℚ) (hv : eqs.floor ≤ eqs.floor * v) : 1 ≤ v := by
      by_contra! hv'
      linarith [mul_lt_mul_of_pos_left hv' eqs.floor_pos]
    have hh := strip _ hleft
    have hh' := strip _ hright
    change 1 ≤ 1 + 2 * x i at hh
    change 1 ≤ 3 - 2 * x i at hh'
    constructor <;> linarith
  have hnode (e : Expr I) (hm : e ∈ eqs.nodes) :
      rate (eqs.aux ⟨e, hm⟩ false false) = eqs.floor * e.eval x := by
    induction e with
    | one =>
      have he := (equalRate_iff hrootPos.ne').mp (hc.nodes ⟨.one, hm⟩)
      simpa [hroot, Expr.eval] using he
    | coordinate i b =>
      have he := (equalRate_iff hrootPos.ne').mp (hc.nodes ⟨.coordinate i b, hm⟩)
      simpa [hbox' i b, Expr.eval] using he
    | add a b ha hb =>
      have he := (sumRate_iff (hne := by simp [aux]) hrootPos.ne').mp (hc.nodes ⟨.add a b, hm⟩)
      rw [he, hdup, ha, hb, Expr.eval, mul_add]
    | mul a b ha hb =>
      have he := (productRate_iff hrootPos.ne').mp (hc.nodes ⟨.mul a b, hm⟩)
      rw [he, ha, hb, hroot, Expr.eval]
      field_simp
  have hcap (e : eqs.Node) (copy : Bool) :
      rate (eqs.aux e copy false) = eqs.floor * e.val.eval x := by
    cases copy
    · exact hnode _ e.property
    · rw [hdup]; exact hnode _ e.property
  refine ⟨hboxIn, ?_, ?_⟩
  · intro e hm
    have he := (equalRate_iff hrootPos.ne').mp (hc.equations ⟨e, hm⟩)
    apply mul_left_cancel₀ eqs.floor_pos.ne'
    rw [← hcap ⟨e.1, eqs.left_mem hm⟩ false, ← hcap ⟨e.2, eqs.right_mem hm⟩ false]
    exact he
  · funext m
    rcases m with ⟨j, b⟩ | ⟨i, b⟩ | ⟨e, copy, b⟩
    · symm
      simpa only [hroot] using hrr j b
    · exact (hbox' i b).symm
    · cases b
      · exact (hcap e copy).symm
      · have hs := haux e copy
        rw [hroot, hcap e copy] at hs
        change eqs.floor * (eqs.capacity - e.val.eval x) = rate (eqs.aux e copy true)
        rw [mul_sub]
        linarith

def BoxLawful (eqs : Equations I) (x : I → ℚ) : Prop := InBox x ∧ eqs.holds x

def BoxStep (eqs : Equations I) (ε : ℚ) (x y : I → ℚ) : Prop :=
  BoxLawful eqs x ∧ BoxLawful eqs y ∧ ∀ i, |x i - y i| < ε

abbrev BoxChain (eqs : Equations I) (ε : ℚ) := Relation.ReflTransGen (BoxStep eqs ε)

def BoxFine (eqs : Equations I) (x y : I → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → BoxChain eqs ε x y

theorem decode_chain (eqs : Equations I) {ε : ℚ} {a b : eqs.Mark → ℚ}
    (h : Chain eqs.tests eqs.floor (2 * eqs.floor * ε) a b) :
    BoxChain eqs ε (eqs.decode a) (eqs.decode b) := by
  refine h.lift eqs.decode (fun p q hstep => ?_)
  have ha := eqs.lawful_decode hstep.1
  have hb := eqs.lawful_decode hstep.2.1
  refine ⟨⟨ha.1, ha.2.1⟩, ⟨hb.1, hb.2.1⟩, fun i => ?_⟩
  have hp : 0 < 2 * eqs.floor := by have := eqs.floor_pos; positivity
  have hdiff : eqs.decode p i - eqs.decode q i =
      (p (eqs.box i false) - q (eqs.box i false)) / (2 * eqs.floor) := by
    simp only [decode, readCube]
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hp]
  exact (div_lt_iff₀ hp).mpr (by
    have h := hstep.2.2 (eqs.box i false)
    simpa only [mul_comm ε] using h)

def variationBound (eqs : Equations I) : ℚ :=
  eqs.floor * ((↑(eqs.nodes.sup Expr.slope) : ℚ) + 2) + 1

theorem variationBound_pos (eqs : Equations I) : 0 < eqs.variationBound := by
  unfold variationBound
  have := eqs.floor_pos
  positivity

theorem encode_variation (eqs : Equations I) {x y : I → ℚ} {τ : ℚ} (hτ : 0 < τ)
    (hx : InBox x) (hy : InBox y) (hclose : ∀ i, |x i - y i| ≤ τ) (m : eqs.Mark) :
    |eqs.encode x m - eqs.encode y m| < eqs.variationBound * τ := by
  have hr := eqs.floor_pos
  have hsup : (0 : ℚ) ≤ (↑(eqs.nodes.sup Expr.slope) : ℚ) := by positivity
  have hp := eqs.variationBound_pos
  rcases m with ⟨j, b⟩ | ⟨i, b⟩ | ⟨e, copy, b⟩
  · change |eqs.floor * 2 ^ (j : ℕ) - eqs.floor * 2 ^ (j : ℕ)| < _
    simpa only [sub_self, abs_zero] using mul_pos hp hτ
  · change |eqs.floor * unitRate x i b - eqs.floor * unitRate y i b| < _
    rw [← mul_sub, abs_mul, abs_of_pos hr, unitRate_sub]
    have hle := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hclose i) (by norm_num : (0 : ℚ) ≤ 2)) hr.le
    apply hle.trans_lt
    rw [← mul_assoc]
    apply mul_lt_mul_of_pos_right _ hτ
    unfold variationBound
    nlinarith
  · have hval : |e.val.eval x - e.val.eval y| ≤ (↑(eqs.nodes.sup Expr.slope) : ℚ) * τ := by
      apply (e.val.eval_variation hx hy hclose).trans
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f := Expr.slope) e.property) hτ.le
    have hle : |eqs.floor * (e.val.eval x - e.val.eval y)| < eqs.variationBound * τ := by
      rw [abs_mul, abs_of_pos hr]
      apply (mul_le_mul_of_nonneg_left hval hr.le).trans_lt
      rw [← mul_assoc]
      apply mul_lt_mul_of_pos_right _ hτ
      unfold variationBound
      nlinarith
    cases b
    · rw [mul_sub] at hle
      exact hle
    · change |eqs.floor * (eqs.capacity - e.val.eval x) -
        eqs.floor * (eqs.capacity - e.val.eval y)| < _
      rw [show eqs.floor * (eqs.capacity - e.val.eval x) - eqs.floor * (eqs.capacity - e.val.eval y) =
        -(eqs.floor * (e.val.eval x - e.val.eval y)) by ring, abs_neg]
      exact hle

theorem encode_has_mesh (eqs : Equations I) {x y : I → ℚ} {ε : ℚ} (hε : 0 < ε)
    (hchain : BoxChain eqs (ε / eqs.variationBound) x y) :
    Chain eqs.tests eqs.floor ε (eqs.encode x) (eqs.encode y) := by
  have hτ : 0 < ε / eqs.variationBound := div_pos hε eqs.variationBound_pos
  refine hchain.lift eqs.encode (fun p q hstep => ⟨eqs.encode_lawful hstep.1.1 hstep.1.2,
    eqs.encode_lawful hstep.2.1.1 hstep.2.1.2, fun m => ?_⟩)
  have h := eqs.encode_variation hτ hstep.1.1 hstep.2.1.1 (fun i => (hstep.2.2 i).le) m
  rwa [mul_comm, div_mul_cancel₀ _ eqs.variationBound_pos.ne'] at h

theorem fine_encode_iff (eqs : Equations I) (x y : I → ℚ) :
    Fine eqs.tests eqs.floor (eqs.encode x) (eqs.encode y) ↔ BoxFine eqs x y := by
  constructor
  · intro h ε hε
    have hpos : 0 < 2 * eqs.floor * ε := by have := eqs.floor_pos; positivity
    simpa using eqs.decode_chain (h _ hpos)
  · intro h ε hε
    exact eqs.encode_has_mesh hε (h _ (div_pos hε eqs.variationBound_pos))

end MovingProjection.OneStateEvents.Equations
