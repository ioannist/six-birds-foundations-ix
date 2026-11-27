import MovingProjection.CalibratedResponses
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Real.Sqrt

/-! A single binary probe distinguishes rational from real reachability:
held square identities give the positive real arc of the Fermat quartic,
while the rational law can only have one nonzero axis coordinate. -/

namespace MovingProjection.FermatProbe

open CalibratedResponses
open scoped BigOperators

abbrev Aux := Fin 5

def refMark : Other Aux := .inr 0
def xMark : Other Aux := .inr 1
def yMark : Other Aux := .inr 2
def uMark : Other Aux := .inr 3
def vMark : Other Aux := .inr 4

def pair : Fin 4 → TimedPair (Other Aux) 2 :=
  fun g =>
    if g = 0 then ⟨uMark, xMark, [refMark], [xMark], rfl, le_rfl⟩
    else if g = 1 then ⟨.inl false, uMark, [refMark], [uMark], rfl, le_rfl⟩
    else if g = 2 then ⟨vMark, yMark, [refMark], [yMark], rfl, le_rfl⟩
    else ⟨.inl true, vMark, [refMark], [vMark], rfl, le_rfl⟩

def catalogue : Catalogue Aux Unit (Fin 4) Unit :=
  ⟨1, pair, fun _ => ((refMark, ()), 1/4), 1/4⟩

def parity : ParityBasis Unit Bool where
  value _ x := if x then 1 else -1
  abs_eq_one _ x := by cases x <;> norm_num
  balance _ := by simp
  orthogonal i j := by cases i; cases j; norm_num [Fintype.sum_bool]

abbrev Native := State catalogue parity

def corner (b : Bool) (p : Mark Aux × Unit) : ℚ :=
  match p.1 with
  | .inl _ => 1/8
  | .inr (.inl t) => if t = b then 1/4 else 0
  | .inr (.inr m) =>
    if m = 0 ∨ (m = 1 ∨ m = 3) ∧ b = false ∨ (m = 2 ∨ m = 4) ∧ b = true
      then 1/4 else 0

theorem corner_lawful (b : Bool) : catalogue.Lawful (corner b) := by
  constructor
  · intro m
    rw [Fintype.sum_unique]
    rcases m with (u | t | m)
    · norm_num [corner]
    · cases t <;> cases b <;> norm_num [corner]
    · simp only [corner]
      split_ifs <;> norm_num
  · intro j
    norm_num [corner, left, catalogue]
  · intro e
    norm_num [corner, catalogue, refMark]
  · intro j
    cases b <;> norm_num [corner, catalogue, toggle]
  · intro g j
    change response (pair g).left (corner b) j = response (pair g).right (corner b) j
    cases j
    fin_cases g <;> cases b <;> decide +kernel

noncomputable def endpoint (b : Bool) : Native :=
  build parity (corner b) (corner_lawful b)

private def signal (m : Other Aux) (s : Native) : ℚ := s.val.law.spectrum (.inr m, ())

private theorem quartic (s : Native) (hp : s.val.profile = profile) :
    signal xMark s ^ 4 + signal yMark s ^ 4 = (1/4 : ℚ)^4 := by
  have h := lawful_state s hp
  have ha : signal refMark s = 1/4 := h.calibrations ()
  have he : signal (.inl false) s + signal (.inl true) s = 1/4 := h.complement ()
  have hu : signal uMark s * signal refMark s = signal xMark s * signal xMark s := by
    simpa [catalogue, pair, response, TimedPair.left, TimedPair.right, signal] using h.comparisons 0 ()
  have hx : signal (.inl false) s * signal refMark s = signal uMark s * signal uMark s := by
    simpa [catalogue, pair, response, TimedPair.left, TimedPair.right, signal] using h.comparisons 1 ()
  have hv : signal vMark s * signal refMark s = signal yMark s * signal yMark s := by
    simpa [catalogue, pair, response, TimedPair.left, TimedPair.right, signal] using h.comparisons 2 ()
  have hy : signal (.inl true) s * signal refMark s = signal vMark s * signal vMark s := by
    simpa [catalogue, pair, response, TimedPair.left, TimedPair.right, signal] using h.comparisons 3 ()
  calc
    _ = (signal xMark s * signal xMark s)^2 + (signal yMark s * signal yMark s)^2 := by ring
    _ = ((signal (.inl false) s + signal (.inl true) s) * signal refMark s) *
        signal refMark s ^ 2 := by
      rw [← hu, ← hv]
      ring_nf
      linear_combination signal refMark s ^ 2 * (-hx - hy)
    _ = _ := by rw [he, ha]; norm_num

private theorem axis (s : Native) (hp : s.val.profile = profile) :
    signal xMark s = 1/4 ∨ signal xMark s = 0 ∨ signal xMark s = -(1/4) := by
  by_cases hx : signal xMark s = 0
  · exact .inr (.inl hx)
  have he := quartic s hp
  have hy : signal yMark s = 0 := by
    by_contra hy
    exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour)
      (signal xMark s) (signal yMark s) (1/4) hx hy (by norm_num) he
  rw [hy] at he
  have hz : (signal xMark s - 1/4) * (signal xMark s + 1/4) *
      (signal xMark s ^ 2 + (1/4 : ℚ)^2) = 0 := by
    linear_combination he
  have hp' : 0 < signal xMark s ^ 2 + (1/4 : ℚ)^2 := by positivity
  rcases mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hp'.ne') with h | h
  · exact .inl (by linarith)
  · exact .inr (.inr (by linarith))

private theorem marked_diag (s : Native) (hp : s.val.profile = profile) :
    s.val.law.marked parity (.inr xMark) (false, ()) (false, ()) =
      (1/9 : ℚ) * (1 + signal xMark s) / 2 := by
  have hs := build_decode s hp
  calc
    _ = (build parity s.val.law.spectrum (lawful_state s hp)).val.law.marked parity
        (.inr xMark) (false, ()) (false, ()) := by rw [hs]
    _ = _ := by
      norm_num [build, law, PhysicalLaw.marked, nativeMarked, ParityBasis.kernel, parity,
        signal, rate, floor, xMark]
      ring

/-- The endpoint gap is measured in actual prepared-table entries. -/
theorem no_chain : ¬ (instrument catalogue parity).Chain (1/72) (endpoint false) (endpoint true) := by
  intro h
  have hold (s : Native) (h : (instrument catalogue parity).Chain (1/72) (endpoint false) s)
      (hp : s.val.profile = profile) : signal xMark s = 1/4 := by
    induction h with
    | refl => rfl
    | @tail u v hu hv ih =>
      have hpu : u.val.profile = profile := le_antisymm
        (hp ▸ hv.profile_le) (EventExperiments.Chain.profile_le hu)
      have hnear := ((instrument catalogue parity).step_iff_near_of_profile_eq (hpu.trans hp.symm)).mp hv
        (.inr xMark) (false, ()) (false, ())
      change |u.val.law.marked parity (.inr xMark) (false, ()) (false, ()) -
        v.val.law.marked parity (.inr xMark) (false, ()) (false, ())| < 1/72 at hnear
      rw [marked_diag u hpu, marked_diag v hp, ih hpu] at hnear
      rcases axis v hp with he | he | he
      · exact he
      · norm_num [he] at hnear
      · norm_num [he] at hnear
  have hEnd := hold _ h rfl
  change (0 : ℚ) = 1/4 at hEnd
  norm_num at hEnd

theorem not_factorable : ¬ (instrument catalogue parity).Factorable (endpoint false) (endpoint true) :=
  fun h => no_chain (h _ (by norm_num))

theorem exactly_one : ∃! g, ((instrument catalogue parity).second g).isSome = true :=
  CalibratedResponses.exactly_one catalogue parity

noncomputable def realArc (t : ℝ) : ℝ × ℝ :=
  ((1/4) * Real.sqrt (Real.sqrt (1-t)), (1/4) * Real.sqrt (Real.sqrt t))

theorem continuous_realArc : Continuous realArc := by
  unfold realArc
  fun_prop

theorem realArc_endpoints : realArc 0 = (1/4,0) ∧ realArc 1 = (0,1/4) := by
  norm_num [realArc]

theorem realArc_quartic {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (realArc t).1^4 + (realArc t).2^4 = (1/4 : ℝ)^4 := by
  have root (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x)^4 = x := by
    rw [show Real.sqrt (Real.sqrt x)^4 = (Real.sqrt (Real.sqrt x)^2)^2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]
  simp only [realArc, mul_pow, root t ht, root (1-t) (sub_nonneg.mpr ht')]
  ring

end MovingProjection.FermatProbe
