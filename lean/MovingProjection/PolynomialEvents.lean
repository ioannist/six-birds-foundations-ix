import MovingProjection.ArithmeticEvents

/-! A polynomial given as an arithmetic term has a finite set of subterms.
Their values form the registers of a local gate system. Register indexing by
subterms makes the evaluation correctness independent of a particular
serialized circuit representation. -/

namespace MovingProjection.OneStateEvents.ArithmeticReduction

variable {I : Type}

inductive Term (I : Type) where
  | zero
  | one
  | var (i : I)
  | add (a b : Term I)
  | neg (a : Term I)
  | mul (a b : Term I)
  deriving DecidableEq

namespace Term

def eval (v : I → ℚ) : Term I → ℚ
  | .zero => 0
  | .one => 1
  | .var i => v i
  | .add a b => a.eval v + b.eval v
  | .neg a => -a.eval v
  | .mul a b => a.eval v * b.eval v

def subterms : Term I → List (Term I)
  | .zero => [.zero]
  | .one => [.one]
  | .var i => [.var i]
  | .add a b => .add a b :: (a.subterms ++ b.subterms)
  | .neg a => .neg a :: a.subterms
  | .mul a b => .mul a b :: (a.subterms ++ b.subterms)

@[simp] theorem self_mem (t : Term I) : t ∈ t.subterms := by
  cases t <;> simp [subterms]

theorem mem_trans {a b c : Term I} (hab : a ∈ b.subterms) (hbc : b ∈ c.subterms) :
    a ∈ c.subterms := by
  induction c with
  | zero => simp [subterms] at hbc; simpa [hbc] using hab
  | one => simp [subterms] at hbc; simpa [hbc] using hab
  | var _ => simp [subterms] at hbc; simpa [hbc] using hab
  | add a b ha hb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hbc ⊢
    rcases hbc with rfl | h | h
    · simpa [subterms] using hab
    · exact Or.inr (Or.inl (ha h))
    · exact Or.inr (Or.inr (hb h))
  | neg a ih =>
    simp only [subterms, List.mem_cons] at hbc ⊢
    rcases hbc with rfl | h
    · simpa [subterms] using hab
    · exact Or.inr (ih h)
  | mul a b ha hb =>
    simp only [subterms, List.mem_cons, List.mem_append] at hbc ⊢
    rcases hbc with rfl | h | h
    · simpa [subterms] using hab
    · exact Or.inr (Or.inl (ha h))
    · exact Or.inr (Or.inr (hb h))

variable [DecidableEq I]

abbrev Register (t : Term I) := ↥t.subterms.toFinset

def top (t : Term I) : t.Register := ⟨t, List.mem_toFinset.mpr t.self_mem⟩

private def child {t sub a : Term I} (hs : sub ∈ t.subterms.toFinset) (ha : a ∈ sub.subterms) :
    t.Register := ⟨a, List.mem_toFinset.mpr (mem_trans ha (List.mem_toFinset.mp hs))⟩

private def gate (t : Term I) : t.Register → Option (Gate t.Register)
  | ⟨.zero, h⟩ => some (.zero ⟨.zero, h⟩)
  | ⟨.one, h⟩ => some (.one ⟨.one, h⟩)
  | ⟨.var _, _⟩ => none
  | ⟨.add a b, h⟩ =>
    some (.add ⟨.add a b, h⟩
      (child (a := a) h (by simp [subterms])) (child (a := b) h (by simp [subterms])))
  | ⟨.neg a, h⟩ =>
    some (.neg ⟨.neg a, h⟩ (child (a := a) h (by simp [subterms])))
  | ⟨.mul a b, h⟩ =>
    some (.mul ⟨.mul a b, h⟩
      (child (a := a) h (by simp [subterms])) (child (a := b) h (by simp [subterms])))

def gates (t : Term I) : List (Gate t.Register) :=
  .zero t.top :: t.subterms.dedup.attach.filterMap (fun a =>
    t.gate ⟨a.val, List.mem_toFinset.mpr (List.mem_dedup.mp a.property)⟩)

private theorem local_gates_iff (t : Term I) (v : t.Register → ℚ) :
    (∀ g ∈ t.gates, g.holds v) ↔
    v t.top = 0 ∧ ∀ a : t.Register, ∀ g, t.gate a = some g → g.holds v := by
  simp only [gates, List.forall_mem_cons, Gate.holds]
  apply and_congr_right
  intro _
  constructor
  · intro h a g hg
    have ha : a.val ∈ t.subterms.dedup := List.mem_dedup.mpr (List.mem_toFinset.mp a.property)
    apply h g
    exact List.mem_filterMap.mpr ⟨⟨a.val, ha⟩, List.mem_attach _ _, hg⟩
  · intro h g hg
    obtain ⟨a, _, he⟩ := List.mem_filterMap.mp hg
    exact h ⟨a.val, List.mem_toFinset.mpr (List.mem_dedup.mp a.property)⟩ g he

theorem solvable_iff_zero (t : Term I) :
    Solvable t.gates ↔ ∃ x : I → ℚ, t.eval x = 0 := by
  classical
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨htop, hlocal⟩ := (local_gates_iff t v).mp hv
    let x (i : I) : ℚ := if h : .var i ∈ t.subterms.toFinset then v ⟨.var i, h⟩ else 0
    have hret (a : Term I) (h : a ∈ t.subterms.toFinset) : v ⟨a, h⟩ = a.eval x := by
      induction a with
      | zero => exact hlocal ⟨.zero, h⟩ (.zero ⟨.zero, h⟩) rfl
      | one => exact hlocal ⟨.one, h⟩ (.one ⟨.one, h⟩) rfl
      | var i => simp only [eval, x, dif_pos h]
      | add a b ha hb =>
        let l := child (a := a) h (by simp [subterms])
        let r := child (a := b) h (by simp [subterms])
        have he : v ⟨.add a b, h⟩ = v l + v r :=
          hlocal ⟨.add a b, h⟩ (.add ⟨.add a b, h⟩ l r) rfl
        have hl : v l = a.eval x := ha l.property
        have hr : v r = b.eval x := hb r.property
        rw [he, hl, hr, eval]
      | neg a ha =>
        let l := child (a := a) h (by simp [subterms])
        have he : v ⟨.neg a, h⟩ = -v l := hlocal ⟨.neg a, h⟩ (.neg ⟨.neg a, h⟩ l) rfl
        have hl : v l = a.eval x := ha l.property
        rw [he, hl, eval]
      | mul a b ha hb =>
        let l := child (a := a) h (by simp [subterms])
        let r := child (a := b) h (by simp [subterms])
        have he : v ⟨.mul a b, h⟩ = v l * v r :=
          hlocal ⟨.mul a b, h⟩ (.mul ⟨.mul a b, h⟩ l r) rfl
        have hl : v l = a.eval x := ha l.property
        have hr : v r = b.eval x := hb r.property
        rw [he, hl, hr, eval]
    exact ⟨x, (hret t t.top.property).symm.trans htop⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun a => a.val.eval x, (local_gates_iff _ _).mpr ⟨hx, ?_⟩⟩
    rintro ⟨a, ha⟩ g hg
    cases a <;> simp only [gate, Option.some.injEq, reduceCtorEq] at hg
    all_goals subst g
    all_goals rfl

theorem native_chain_iff_rational_zero (t : Term I) :
    (compile t.gates).NativeChain (2 * (compile t.gates).floor)
      (endpoint t.gates false) (endpoint t.gates true) ↔ ∃ x, t.eval x = 0 :=
  (native_chain_iff_solvable t.gates).trans t.solvable_iff_zero

theorem native_fine_iff_rational_zero (t : Term I) :
    (∀ ε : ℚ, 0 < ε → (compile t.gates).NativeChain ε
      (endpoint t.gates false) (endpoint t.gates true)) ↔ ∃ x, t.eval x = 0 :=
  (native_fine_iff_solvable t.gates).trans t.solvable_iff_zero

theorem native_chain_iff_rational_zero_of_le (t : Term I) {ε : ℚ}
    (hε : 0 < ε) (hle : ε ≤ 2 * (compile t.gates).floor) :
    (compile t.gates).NativeChain ε (endpoint t.gates false) (endpoint t.gates true) ↔
      ∃ x, t.eval x = 0 :=
  (native_chain_iff_solvable_of_le t.gates hε hle).trans t.solvable_iff_zero

end Term

end MovingProjection.OneStateEvents.ArithmeticReduction
