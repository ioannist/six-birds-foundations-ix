import MovingProjection.CommitLate

/-! Geometric form of the timing criterion. Take the closure of the
rational projected tables before computing connected components. -/

namespace MovingProjection

open Set
open scoped BigOperators

private theorem fineMesh_iff_component {S K : Type*} [MetricSpace K] [CompactSpace K]
    (f : S → K) (dense : DenseRange f) (a b : S) :
    (∀ ε : ℝ, 0 < ε → Relation.ReflTransGen (fun u v => dist (f u) (f v) < ε) a b) ↔
      f b ∈ connectedComponent (f a) := by
  constructor
  · intro H
    rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter]
    intro U
    obtain ⟨r, hr, gap⟩ := Metric.exists_pos_forall_lt_edist U.2.1.1.isCompact
      U.2.1.2.isClosed_compl disjoint_compl_right
    have hpos : 0 < (r : ℝ) := NNReal.coe_pos.mpr hr
    have h := H r hpos
    clear H
    induction h with
    | refl => exact U.2.2
    | @tail u v _ huv ih =>
      by_contra hv
      have hg := gap (f u) ih (f v) hv
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hg
      exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal huv.le)) hg
  · intro hc ε hε
    by_contra hn
    let C := connectedComponent (f a)
    let reaches (u : S) := Relation.ReflTransGen (fun v w => dist (f v) (f w) < ε) a u
    let A := ⋃ u : {u : S // reaches u}, Metric.ball (f u.val) (ε/3)
    let B := ⋃ u : {u : S // ¬ reaches u}, Metric.ball (f u.val) (ε/3)
    have hr : 0 < ε/3 := by positivity
    have cover : C ⊆ A ∪ B := by
      intro c _
      obtain ⟨u, hu⟩ := Metric.denseRange_iff.mp dense c _ hr
      by_cases h : reaches u
      · exact Or.inl (mem_iUnion.2 ⟨⟨u,h⟩, hu⟩)
      · exact Or.inr (mem_iUnion.2 ⟨⟨u,h⟩, hu⟩)
    have hA : (C ∩ A).Nonempty := ⟨f a, mem_connectedComponent,
      mem_iUnion.2 ⟨⟨a,.refl⟩, Metric.mem_ball_self hr⟩⟩
    have hB : (C ∩ B).Nonempty := ⟨f b, hc,
      mem_iUnion.2 ⟨⟨b,hn⟩, Metric.mem_ball_self hr⟩⟩
    obtain ⟨c, _, ha, hb⟩ := isPreconnected_connectedComponent A B
      (isOpen_iUnion fun _ => Metric.isOpen_ball) (isOpen_iUnion fun _ => Metric.isOpen_ball)
      cover hA hB
    obtain ⟨u, hu⟩ := mem_iUnion.1 ha
    obtain ⟨v, hv⟩ := mem_iUnion.1 hb
    apply v.2 (u.2.tail ?_)
    have h := dist_triangle (f u.val) c (f v.val)
    have hu' := Metric.mem_ball.mp hu
    have hv' := Metric.mem_ball.mp hv
    rw [dist_comm] at hu'
    linarith

namespace EventExperiments

variable {M I X R Γ Δ : Type*} {n : ℕ}
  [Fintype M] [Fintype I] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
  [DecidableEq M] [DecidableEq I] [DecidableEq X] [Nonempty X] [Nonempty R]

variable (E : EventExperiments M I X R Γ Δ)

abbrev ProfileState (p : Capabilities M X R Γ Δ n) := {s : E.State n // s.val.profile = p}

/-- Closure in the real sup metric of the projected marked tables of lawful
rational states at this profile. -/
def ProjectedClosure (p : Capabilities M X R Γ Δ n) : Set (M × X × X → ℝ) :=
  closure (range fun s : E.ProfileState p => embed (E.projected s.val))

omit [Fintype Γ] [Fintype Δ] [Nonempty X] [Nonempty R] in
private theorem projected_mem (p : Capabilities M X R Γ Δ n) (s : E.ProfileState p) :
    embed (E.projected s.val) ∈ E.ProjectedClosure p := subset_closure (mem_range_self s)

def point (p : Capabilities M X R Γ Δ n) (s : E.ProfileState p) : E.ProjectedClosure p :=
  ⟨embed (E.projected s.val), E.projected_mem p s⟩

omit [Fintype Γ] [Fintype Δ] [Nonempty X] [Nonempty R] in
theorem projectedClosure_mono (a b : E.State n) (h : a.val.profile ≤ b.val.profile) :
    E.ProjectedClosure b.val.profile ⊆ E.ProjectedClosure a.val.profile := by
  apply closure_mono
  rintro _ ⟨s, rfl⟩
  have hs : a.val.profile ≤ s.val.val.profile := by rw [s.property]; exact h
  let t := E.atSource a s.val hs
  exact ⟨⟨t,rfl⟩, rfl⟩

omit [Fintype Γ] [Fintype Δ] [Nonempty R] in
private theorem compact_projection (p : Capabilities M X R Γ Δ n) :
    IsCompact (E.ProjectedClosure p) := by
  apply (isCompact_closedBall (0 : M × X × X → ℝ) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  rintro _ ⟨s, rfl⟩
  apply Metric.mem_closedBall.2
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).2
  rintro ⟨m,x,y⟩
  change dist ((E.projected s.val (m,x,y) : ℚ) : ℝ) 0 ≤ 1
  have legalRate := s.val.val.legal.2.2.1
  have h₀ : 0 ≤ s.val.val.law.rate m := E.native.δ_pos.le.trans (legalRate.1 m)
  have h₁ : s.val.val.law.rate m ≤ 1 := by
    rw [← legalRate.2.1]
    exact Finset.single_le_sum (fun j _ => E.native.δ_pos.le.trans (legalRate.1 j))
      (Finset.mem_univ m)
  have hk := E.native.parity.kernel_bounds
    ((spectrum_budget s.val.val.legal.2.2.2.1 m).trans_lt E.native.κ_lt_one) x y
  have hbound : |E.projected s.val (m,x,y)| ≤ 1 := by
    rw [projected, abs_of_nonneg (mul_nonneg h₀ hk.1)]
    exact (mul_le_of_le_one_right h₀ hk.2).trans h₁
  rw [Real.dist_eq, sub_zero]
  exact_mod_cast hbound

omit [Fintype Γ] [Fintype Δ] [Nonempty X] [Nonempty R] in
private theorem point_dense (p : Capabilities M X R Γ Δ n) : DenseRange (E.point p) := by
  apply Metric.denseRange_iff.2
  intro b r hr
  obtain ⟨v, ⟨s, rfl⟩, hv⟩ := Metric.mem_closure_iff.1 b.property r hr
  exact ⟨s, hv⟩

omit [Fintype Γ] [Fintype Δ] in
/-- Fixed-profile fine reachability is exactly connected-component membership
in the closure of the rational projected law space. -/
theorem fixedProfile_iff_projectedComponent (p : Capabilities M X R Γ Δ n)
    (a b : E.ProfileState p) :
    E.Factorable a.val b.val ↔ E.point p b ∈ connectedComponent (E.point p a) := by
  letI : CompactSpace (E.ProjectedClosure p) := isCompact_iff_compactSpace.mp (E.compact_projection p)
  rw [← fineMesh_iff_component (E.point p) (E.point_dense p)]
  constructor
  · intro H ε hε
    obtain ⟨η, hη₀, hη⟩ := exists_rat_btwn (show (0 : ℝ) < ε / (Fintype.card R + 1) by positivity)
    have hηQ : (0 : ℚ) < η := by exact_mod_cast hη₀
    have hbound : (Fintype.card R : ℝ) * (η : ℝ) ≤ ε := by
      have h := (lt_div_iff₀ (show (0 : ℝ) < Fintype.card R + 1 by positivity)).1 hη
      linarith
    have map (s : E.State n) (hs : s.val.profile = p) (h : E.Chain η a.val s) :
        Relation.ReflTransGen (fun u v => dist (E.point p u) (E.point p v) < ε)
          a (⟨s, hs⟩ : E.ProfileState p) := by
      induction h with
      | refl => exact .refl
      | @tail u v hu huv ih =>
        have hup : u.val.profile = p :=
          le_antisymm (hs ▸ huv.profile_le) (a.property ▸ Chain.profile_le hu)
        have hn := (E.step_iff_near_of_profile_eq (hup.trans hs.symm)).1 huv
        apply (ih hup).tail
        change dist (embed (E.projected u)) (embed (E.projected v)) < ε
        apply (dist_pi_lt_iff hε).2
        intro j
        have h := E.projected_near u v hn j
        rw [Real.dist_eq]
        have hd : |embed (E.projected u) j - embed (E.projected v) j| <
            (Fintype.card R : ℝ) * (η : ℝ) := by
          change |((E.projected u j : ℚ) : ℝ) - ((E.projected v j : ℚ) : ℝ)| < _
          exact_mod_cast h
        exact hd.trans_le hbound
    exact map b.val b.property (H η hηQ)
  · intro H ε hε
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    let lift (s : E.ProfileState p) : E.State n := E.atSource a.val s.val
      ((a.property.trans s.property.symm).le)
    have mesh : E.Chain ε (lift a) (lift b) := by
      apply (H ε hεR).lift lift
      intro u v hd
      have hu := Capabilities.le_coordinates.1 (a.property.trans u.property.symm).le
      have hv := Capabilities.le_coordinates.1 (a.property.trans v.property.symm).le
      refine Or.inl ⟨rfl, E.carry_near a.val u.val v.val
        hu.2.2.1 hu.2.2.2 hv.2.2.1 hv.2.2.2 (fun j => ?_)⟩
      have h := (dist_pi_lt_iff hεR).1 hd j
      rw [Real.dist_eq] at h
      change |((E.projected u.val j : ℚ) : ℝ) - ((E.projected v.val j : ℚ) : ℝ)| < _ at h
      exact_mod_cast h
    have hstart : lift a = a.val :=
      Subtype.ext (Protocol.State.ext rfl (PhysicalLaw.ext rfl rfl rfl))
    rw [hstart] at mesh
    exact mesh.trans (E.fixedProfile_registerChain hε (a.property.trans b.property.symm) ⟨rfl,rfl⟩)

/-- If the source profile precedes or equals the target profile, test
component membership in the source closure using the target's projected
table. Failure of the directed profile inequality rules out every chain by
`Chain.profile_le`. -/
theorem factorable_iff_projectedComponent (a b : E.State n)
    (h : a.val.profile ≤ b.val.profile) :
    E.Factorable a b ↔
      E.point a.val.profile ⟨E.atSource a b h, rfl⟩ ∈
        connectedComponent (E.point a.val.profile ⟨a,rfl⟩) :=
  (E.factorable_iff_atSource a b h).trans
    (E.fixedProfile_iff_projectedComponent a.val.profile ⟨a,rfl⟩ ⟨E.atSource a b h,rfl⟩)

/-- For three lawful states with `a.profile ≤ early.profile ≤ b.profile`
(on the underlying states), compare reachability from each of the two
starting states to `b` using the two source closures. A lawful commitment
from `a` to `early` supplies the first inequality and preserves the law, so
the timing application compares the same projected endpoints. -/
theorem commitLate_iff_projectedComponents (a early b : E.State n)
    (ha : a.val.profile ≤ early.val.profile) (hb : early.val.profile ≤ b.val.profile) :
    (E.Factorable a b ∧ ¬ E.Factorable early b) ↔
      (E.point a.val.profile ⟨E.atSource a b (ha.trans hb), rfl⟩ ∈
        connectedComponent (E.point a.val.profile ⟨a,rfl⟩) ∧
      E.point early.val.profile ⟨E.atSource early b hb,rfl⟩ ∉
        connectedComponent (E.point early.val.profile ⟨early,rfl⟩)) := by
  rw [E.factorable_iff_projectedComponent a b (ha.trans hb),
    E.factorable_iff_projectedComponent early b hb]

end EventExperiments

end MovingProjection
