import MovingProjection.EventCompiler
import MovingProjection.NativeEvents

/-! The 3-CNF reduction. Its semantic equivalence holds for every width;
the width bound is used for the binary input size in the accompanying proof. -/

namespace MovingProjection.OneStateEvents

namespace SignedExpr

variable {I : Type}

abbrev Pair (I : Type) := Expr I × Expr I

def eval (p : Pair I) (x : I → ℚ) : ℚ := p.1.eval x - p.2.eval x

def zero : Pair I := (.one, .one)
def one : Pair I := (.add .one .one, .one)
def coord (i : I) : Pair I := (.coordinate i false, .one)

def add (a b : Pair I) : Pair I := (.add a.1 b.1, .add a.2 b.2)
def neg (a : Pair I) : Pair I := (a.2, a.1)
def sub (a b : Pair I) : Pair I := add a (neg b)
def mul (a b : Pair I) : Pair I :=
  (.add (.mul a.1 b.1) (.mul a.2 b.2), .add (.mul a.1 b.2) (.mul a.2 b.1))

@[simp] theorem eval_zero (x : I → ℚ) : eval zero x = 0 := by norm_num [zero, eval, Expr.eval]
@[simp] theorem eval_one (x : I → ℚ) : eval one x = 1 := by norm_num [one, eval, Expr.eval]
@[simp] theorem eval_coord (i : I) (x : I → ℚ) : eval (coord i) x = 2 * x i := by
  simp [coord, eval, Expr.eval, unitRate]

@[simp] theorem eval_add (a b : Pair I) (x : I → ℚ) : eval (add a b) x = eval a x + eval b x := by
  simp only [add, eval, Expr.eval]
  ring

@[simp] theorem eval_neg (a : Pair I) (x : I → ℚ) : eval (neg a) x = -eval a x := by
  simp only [neg, eval]
  ring

@[simp] theorem eval_sub (a b : Pair I) (x : I → ℚ) : eval (sub a b) x = eval a x - eval b x := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem eval_mul (a b : Pair I) (x : I → ℚ) : eval (mul a b) x = eval a x * eval b x := by
  simp only [mul, eval, Expr.eval]
  ring

end SignedExpr

namespace Equations

variable {I : Type} [DecidableEq I] [Fintype I]

noncomputable def nativePoint (eqs : Equations I) (x : I → ℚ) (hx : eqs.BoxLawful x) :
    EventState eqs.tests eqs.floor eqs.floor_pos :=
  liftEventState eqs.floor_pos ⟨eqs.encode x, eqs.encode_lawful hx.1 hx.2⟩

abbrev NativeChain (eqs : Equations I) (ε : ℚ)
    (a b : EventState eqs.tests eqs.floor eqs.floor_pos) :=
  Relation.ReflTransGen (NativeEventStep ε) a b

theorem nativeChain_mono (eqs : Equations I) {ε η : ℚ}
    {a b : EventState eqs.tests eqs.floor eqs.floor_pos} (h : eqs.NativeChain ε a b)
    (hle : ε ≤ η) : eqs.NativeChain η a b :=
  h.mono (fun _ _ hs => hs.mono hle)

theorem nativePoint_chain_iff (eqs : Equations I) {x y : I → ℚ}
    (hx : eqs.BoxLawful x) (hy : eqs.BoxLawful y) (ε : ℚ) :
    eqs.NativeChain ε (eqs.nativePoint x hx) (eqs.nativePoint y hy) ↔
      Chain eqs.tests eqs.floor ε (eqs.encode x) (eqs.encode y) :=
  native_event_chain_iff

theorem nativePoint_fine_iff (eqs : Equations I) {x y : I → ℚ}
    (hx : eqs.BoxLawful x) (hy : eqs.BoxLawful y) :
    (∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (NativeEventStep ε)
      (eqs.nativePoint x hx) (eqs.nativePoint y hy)) ↔ eqs.BoxFine x y := by
  rw [← eqs.fine_encode_iff x y]
  exact ⟨fun h ε hε => (eqs.nativePoint_chain_iff hx hy ε).mp (h ε hε),
    fun h ε hε => (eqs.nativePoint_chain_iff hx hy ε).mpr (h ε hε)⟩

end Equations

namespace BooleanReduction

open ClauseReconfiguration

variable {I : Type}

def clauseEquation : Clause I → SignedExpr.Pair I
  | [] => SignedExpr.one
  | lit :: suffix => SignedExpr.mul (.coordinate lit.1 lit.2, .one) (clauseEquation suffix)

theorem clauseEquation_eval (c : Clause I) (x : I → ℚ) :
    SignedExpr.eval (clauseEquation c) x = (c.map fun lit => literalRate 1 x lit - 1).prod := by
  induction c with
  | nil => simp [clauseEquation]
  | cons a c h =>
    have ha : unitRate x a.1 a.2 = literalRate 1 x a := by
      cases hb : a.2 <;> simp [unitRate, literalRate, hb]
    simp only [clauseEquation, SignedExpr.eval_mul, List.map_cons, List.prod_cons, h]
    change (unitRate x a.1 a.2 - 1) * _ = _
    rw [ha]

def compile (f : Formula I) : Equations I := f.map clauseEquation

theorem lawful_iff (f : Formula I) (x : I → ℚ) :
    (compile f).BoxLawful x ↔ ClauseReconfiguration.Lawful f x := by
  unfold Equations.BoxLawful ClauseReconfiguration.Lawful
  apply and_congr_right
  intro _
  simp only [Equations.holds, compile, List.mem_map]
  constructor
  · intro h c hc
    apply (clause_product_iff (one_ne_zero : (1 : ℚ) ≠ 0) x c).mp
    rw [← clauseEquation_eval, SignedExpr.eval, sub_eq_zero]
    exact h _ ⟨c, hc, rfl⟩
  · rintro h _ ⟨c, hc, rfl⟩
    rw [← sub_eq_zero]
    change SignedExpr.eval (clauseEquation c) x = 0
    rw [clauseEquation_eval]
    exact (clause_product_iff (one_ne_zero : (1 : ℚ) ≠ 0) x c).mpr (h c hc)

theorem cube_chain_iff (f : Formula I) (τ : ℚ) (x y : I → ℚ) :
    (compile f).BoxChain τ x y ↔ MeshChain f τ x y := by
  have h (p q : I → ℚ) : (compile f).BoxStep τ p q ↔
      ClauseReconfiguration.SmallStep f τ p q := by
    simp only [Equations.BoxStep, ClauseReconfiguration.SmallStep, lawful_iff]
  exact ⟨fun c => c.mono (fun _ _ e => (h _ _).mp e),
    fun c => c.mono (fun _ _ e => (h _ _).mpr e)⟩

variable [DecidableEq I] [Fintype I]

noncomputable def endpoint (f : Formula I) (a : I → Bool) (ha : Satisfies f a) :=
  (compile f).nativePoint (corner a) ((lawful_iff f _).mpr (corner_lawful ha))

theorem endpoints_distinct (f : Formula I) {a b : I → Bool}
    (ha : Satisfies f a) (hb : Satisfies f b) (hne : a ≠ b) :
    endpoint f a ha ≠ endpoint f b hb := by
  intro he
  have hr := congrArg (fun u => (compile f).decode u.val.law.rate) he
  change (compile f).decode ((compile f).encode (corner a)) =
    (compile f).decode ((compile f).encode (corner b)) at hr
  simp only [Equations.decode_encode] at hr
  apply hne
  funext i
  exact bit_injective (congrFun hr i)

/-- Exact reduction in the original physical metric at a supplied positive
tolerance. The event states use exactly one or two words of duration two. -/
theorem native_chain_iff_flips (f : Formula I) {a b : I → Bool}
    (hf : NoTautologies f) (ha : Satisfies f a) (hb : Satisfies f b) :
    (compile f).NativeChain (2 * (compile f).floor)
      (endpoint f a ha) (endpoint f b hb) ↔ FlipChain f a b := by
  let eqs := compile f
  have ha' := (lawful_iff f _).mpr (corner_lawful ha)
  have hb' := (lawful_iff f _).mpr (corner_lawful hb)
  rw [endpoint, endpoint, eqs.nativePoint_chain_iff ha' hb']
  constructor
  · intro h
    have h' : eqs.BoxChain 1 (corner a) (corner b) := by
      have hc : Chain eqs.tests eqs.floor (2 * eqs.floor * 1)
          (eqs.encode (corner a)) (eqs.encode (corner b)) := by simpa using h
      simpa using eqs.decode_chain hc
    exact flips_of_unit_chain (corner_lawful ha) (corner_compatible a) (corner_compatible b)
      ((cube_chain_iff f 1 _ _).mp h')
  · intro h
    apply (eqs.fine_encode_iff _ _).mpr _ _ (mul_pos (by norm_num) eqs.floor_pos)
    intro ε hε
    exact (cube_chain_iff f ε _ _).mpr ((fine_iff_flips hf ha).mpr h ε hε)

theorem native_fine_iff_flips (f : Formula I) {a b : I → Bool}
    (hf : NoTautologies f) (ha : Satisfies f a) (hb : Satisfies f b) :
    (∀ ε : ℚ, 0 < ε → Relation.ReflTransGen (NativeEventStep ε)
      (endpoint f a ha) (endpoint f b hb)) ↔ FlipChain f a b := by
  let eqs := compile f
  rw [endpoint, endpoint, eqs.nativePoint_fine_iff]
  exact ((forall_congr' fun ε => imp_congr_right fun _ => cube_chain_iff f ε _ _)).trans
    (fine_iff_flips hf ha)

theorem native_chain_iff_flips_of_le (f : Formula I) {a b : I → Bool}
    (hf : NoTautologies f) (ha : Satisfies f a) (hb : Satisfies f b)
    {ε : ℚ} (hε : 0 < ε) (hle : ε ≤ 2 * (compile f).floor) :
    (compile f).NativeChain ε (endpoint f a ha) (endpoint f b hb) ↔ FlipChain f a b := by
  constructor
  · intro h
    exact (native_chain_iff_flips f hf ha hb).mp ((compile f).nativeChain_mono h hle)
  · intro h
    exact (native_fine_iff_flips f hf ha hb).mpr h ε hε

end BooleanReduction

end MovingProjection.OneStateEvents
