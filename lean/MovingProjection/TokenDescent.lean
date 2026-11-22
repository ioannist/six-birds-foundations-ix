import MovingProjection.WitnessInput

/-! Deterministic rational realizers of the two physical laws in the rewrite
witness. Each token update is a self-map and descends through the declared
source and target relations. -/

namespace MovingProjection.Example

open scoped BigOperators

abbrev MarkedState := Mark × Bool × Cell
abbrev Token := Mark × Fin 16 × Cell

def stayCount (newLaw : Bool) (m : Mark) : ℕ :=
  match m.val with
  | 0 | 1 => 10
  | 2 => if newLaw then 9 else 7
  | _ => 9

def baseDraw (newLaw : Bool) (m : Mark) (x : Bool) (t : Fin 16) : Bool :=
  if t.val < stayCount newLaw m then x else !x

def registerDraw (m : Mark) (x y : Bool) (u t : Cell) : Cell :=
  if m = 2 ∧ x = false ∧ y = false ∧ u.val < 2 ∧ t.val < 2 then u else t

def tokenUpdate (newLaw : Bool) (t : Token) (s : MarkedState) : MarkedState :=
  let y := baseDraw newLaw t.1 s.2.1 t.2.1
  (t.1,y,registerDraw t.1 s.2.1 y s.2.2 t.2.2)

def rewriteSourceRelation : Setoid MarkedState := Setoid.ker fun s => s.2.1

def rewriteTargetRelation : Setoid MarkedState := Setoid.ker fun s => (s.1,s.2.1)

theorem token_descends (newLaw : Bool) (t : Token) (x y : MarkedState)
    (h : rewriteSourceRelation.r x y) :
    rewriteTargetRelation.r (tokenUpdate newLaw t x) (tokenUpdate newLaw t y) := by
  change x.2.1 = y.2.1 at h
  change (t.1,baseDraw newLaw t.1 x.2.1 t.2.1) =
    (t.1,baseDraw newLaw t.1 y.2.1 t.2.1)
  rw [h]

theorem token_source_class_nontrivial :
    ∃ x y : MarkedState, x ≠ y ∧ rewriteSourceRelation.r x y :=
  ⟨(0,false,0),(0,false,1),by decide,rfl⟩

theorem rewrite_changes_tokenized_projection :
    ¬ rewriteTargetRelation.r (tokenUpdate false (2,7,0) (0,false,0))
      (tokenUpdate true (2,7,0) (0,false,0)) := by
  change (2,true) ≠ ((2 : Mark),false)
  decide

private theorem baseDraw_mass (newLaw : Bool) (m : Mark) (x y : Bool) :
    (∑ t : Fin 16, if baseDraw newLaw m x t = y then (1 : ℚ) else 0) / 16 =
      parity.kernel (fun i => spectrum (1/4) (if newLaw then 1/8 else -1/8) (m,i)) x y := by
  cases newLaw <;> fin_cases m <;> cases x <;> cases y <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    norm_num [baseDraw, stayCount, spectrum, parity, ParityBasis.kernel]

private theorem registerDraw_mass (m : Mark) (x y : Bool) (u v : Cell) :
    (∑ t : Cell, if registerDraw m x y u t = v then (1 : ℚ) else 0) / 4 =
      table true m x y u v := by
  by_cases h : m = 2 ∧ x = false ∧ y = false
  · fin_cases u <;> fin_cases v <;>
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
      norm_num [registerDraw, table, h, localGate, Fin.ext_iff, Fin.val_succ]
  · have e (t : Cell) : registerDraw m x y u t = t := by
      unfold registerDraw
      exact if_neg fun H => h ⟨H.1,H.2.1,H.2.2.1⟩
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [table,h]

def tokenProbability (newLaw : Bool) (m : Mark) (x y : Bool) (u v : Cell) : ℚ :=
  (∑ k : Mark, ∑ t : Fin 16, ∑ s : Cell,
    if tokenUpdate newLaw (k,t,s) (0,x,u) = (m,y,v) then 1 else 0) / 256

theorem tokenProbability_correct (newLaw : Bool) (m : Mark) (x y : Bool) (u v : Cell) :
    tokenProbability newLaw m x y u v =
      (law true (1/4) (if newLaw then 1/8 else -1/8)).marked parity m (x,u) (y,v) := by
  have count : (∑ k : Mark, ∑ t : Fin 16, ∑ s : Cell,
      if tokenUpdate newLaw (k,t,s) (0,x,u) = (m,y,v) then (1 : ℚ) else 0) =
      (∑ t : Fin 16, if baseDraw newLaw m x t = y then 1 else 0) *
        (∑ s : Cell, if registerDraw m x y u s = v then 1 else 0) := by
    have inner (k : Mark) (t : Fin 16) (s : Cell) :
        (if tokenUpdate newLaw (k,t,s) (0,x,u) = (m,y,v) then (1 : ℚ) else 0) =
          if k = m then
            (if baseDraw newLaw m x t = y then 1 else 0) *
              (if registerDraw m x y u s = v then 1 else 0)
          else 0 := by
      by_cases hk : k = m
      · subst k
        by_cases ht : baseDraw newLaw m x t = y <;> simp [tokenUpdate, ht]
      · simp [tokenUpdate, hk]
    simp only [inner, Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hBase := baseDraw_mass newLaw m x y
  have hReg := registerDraw_mass m x y u v
  rw [tokenProbability, count]
  change _ = (1/4 : ℚ) * parity.kernel
    (fun i => spectrum (1/4) (if newLaw then 1/8 else -1/8) (m,i)) x y * table true m x y u v
  rw [← hBase, ← hReg]
  ring

theorem tokenization_returns_both_rewrite_laws (m : Mark) (x y : Bool) (u v : Cell) :
    tokenProbability false m x y u v = (experiment.readouts gated).trial m (x,u) (y,v) ∧
    tokenProbability true m x y u v = (experiment.readouts rewritten).trial m (x,u) (y,v) :=
  ⟨tokenProbability_correct false m x y u v,tokenProbability_correct true m x y u v⟩

end MovingProjection.Example
