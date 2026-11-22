import MovingProjection.Experiments

/-! The projected instrument's word tests return exact native trajectory
probabilities after summing the hidden register. -/

namespace MovingProjection

open scoped BigOperators

variable {M I X R : Type*} [Fintype I] [Fintype X] [Fintype R]
  [DecidableEq I] [DecidableEq X]

def nativeWordEndpoint (P : M → X × R → X × R → ℚ) :
    List M → X × R → X → ℚ
  | [], s, y => if s.1 = y then 1 else 0
  | m :: w, s, y => ∑ t, P m s t * nativeWordEndpoint P w t y

def projectedWordEndpoint (Q : M → X → X → ℚ) : List M → X → X → ℚ
  | [], x, y => if x = y then 1 else 0
  | m :: w, x, y => ∑ z, Q m x z * projectedWordEndpoint Q w z y

theorem projectedWordEndpoint_nonempty (Q : ParityBasis I X) (a : M → I → ℚ)
    (m : M) (w : List M) (s t : X) :
    projectedWordEndpoint (fun z => Q.kernel (a z)) (m::w) s t =
      Q.nonemptyWord a m w s t := by
  induction w generalizing m s with
  | nil =>
    simp [projectedWordEndpoint, ParityBasis.nonemptyWord, mul_ite]
  | cons next rest ih =>
    change (∑ z, Q.kernel (a m) s z *
      projectedWordEndpoint (fun j => Q.kernel (a j)) (next::rest) z t) = _
    simp_rw [ih]
    rfl

theorem nativeWordEndpoint_factor (b : ParityBasis I X) (a : M → I → ℚ)
    (rate : M → ℚ) (reg : Register M X R)
    (hr : ∀ m x y u, ∑ v, reg m x y u v = 1) (w : List M) (s : X × R) (y : X) :
    nativeWordEndpoint (nativeMarked b a rate reg) w s y =
      (w.map rate).prod * projectedWordEndpoint (fun m => b.kernel (a m)) w s.1 y := by
  induction w generalizing s with
  | nil => simp [nativeWordEndpoint, projectedWordEndpoint]
  | cons m w ih =>
    rcases s with ⟨x,u⟩
    simp only [nativeWordEndpoint, ih, List.map_cons, List.prod_cons, projectedWordEndpoint]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    have hcore : (∑ v, nativeMarked b a rate reg m (x,u) (z,v) *
      ((w.map rate).prod * projectedWordEndpoint (fun m => b.kernel (a m)) w z y)) =
        (∑ v, nativeMarked b a rate reg m (x,u) (z,v)) *
          ((w.map rate).prod * projectedWordEndpoint (fun m => b.kernel (a m)) w z y) :=
      (Finset.sum_mul _ _ _).symm
    rw [hcore, native_projection _ _ _ _ _ _ _ _ (hr m x z u)]
    ring

theorem projectedWord_row_sum (Q : M → X → X → ℚ) (hQ : ∀ m x, ∑ y, Q m x y = 1)
    (w : List M) (x : X) :
    ∑ y, projectedWordEndpoint Q w x y = 1 := by
  induction w generalizing x with
  | nil =>
    simp [projectedWordEndpoint, eq_comm (a := x)]
  | cons m w ih =>
    simp only [projectedWordEndpoint]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih, mul_one, hQ]

theorem NativeExperiments.native_word_mass {Γ Δ : Type*}
    [Fintype M] [DecidableEq M] [Nonempty X] (D : NativeExperiments M I X R Γ Δ)
    {n : ℕ} (s : D.protocol.State n) (w : List M) (x : X × R) :
    (∑ y, nativeWordEndpoint (s.law.marked D.parity) w x y) = (w.map s.law.rate).prod := by
  let a (m : M) (i : I) := s.law.spectrum (m,i)
  let P := nativeMarked D.parity a s.law.rate s.law.register
  have hrows := s.legal.2.2.2.2.1.2.1
  change (∑ y, nativeWordEndpoint P w x y) = _
  simp_rw [P, nativeWordEndpoint_factor D.parity a _ _ hrows]
  rw [← Finset.mul_sum, projectedWord_row_sum _ (fun m => D.parity.kernel_row_sum (a m)), mul_one]

theorem NativeExperiments.licensed_trajectory_test {Γ Δ : Type*}
    [Fintype M] [DecidableEq M] [Nonempty X] (D : NativeExperiments M I X R Γ Δ)
    {n : ℕ} (s : D.protocol.State n) {g : Γ} (hg : g ∈ s.profile.licenses)
    (x : X × R) (y : X) :
    nativeWordEndpoint (s.law.marked D.parity) (D.license g).left x y =
      nativeWordEndpoint (s.law.marked D.parity) (D.license g).right x y := by
  have H := D.license_measured s hg
  have hr := s.legal.2.2.2.2.1.2.1
  let a (m : M) (i : I) := s.law.spectrum (m,i)
  let P := nativeMarked D.parity a s.law.rate s.law.register
  change nativeWordEndpoint P (D.license g).left x y = nativeWordEndpoint P (D.license g).right x y
  rw [nativeWordEndpoint_factor D.parity a _ _ hr, nativeWordEndpoint_factor D.parity a _ _ hr, H.1]
  simp only [TimedPair.left, TimedPair.right, projectedWordEndpoint_nonempty]
  exact congrArg (fun K : X → X → ℚ => ((D.license g).right.map s.law.rate).prod * K x.1 y) H.2

theorem NativeExperiments.published_word_ratio {Γ Δ : Type*}
    [Fintype M] [DecidableEq M] [Nonempty X] (D : NativeExperiments M I X R Γ Δ)
    {n : ℕ} (s : D.protocol.State n) {e : Δ} (he : e ∈ s.profile.published)
    {p : TimedPair M D.horizon} {c : ℚ} {hp : 0 < c} (hquery : D.audit e = .ratio p c hp)
    (x : X × R) :
    (∑ y, nativeWordEndpoint (s.law.marked D.parity) p.left x y) =
      c * (∑ y, nativeWordEndpoint (s.law.marked D.parity) p.right x y) := by
  rw [D.native_word_mass, D.native_word_mass]
  exact D.published_ratio s he hquery

end MovingProjection
