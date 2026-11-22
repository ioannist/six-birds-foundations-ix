import MovingProjection.LogEquations
import MovingProjection.RationalKernel

/-! Completeness of the integer contraction test for a converging sign chart. -/

namespace MovingProjection

open Filter Matrix
open scoped BigOperators Topology

variable {I α : Type*} [Fintype I] [DecidableEq I]

theorem contracts_of_limit (tests : List (MonomialTest I))
    {l : Filter α} [l.NeBot] (u : α → I → ℝ) (x : I → ℝ) (s : Finset I)
    (hs : ∀ᶠ a in l, realSupport (u a) = s)
    (hlimit : ∀ i, Tendsto (fun a => u a i) l (𝓝 (x i)))
    (hlegal : ∀ᶠ a in l, ∀ r ∈ tests,
      realMonomial r.row.lhs (u a) = (r.ratio : ℝ) * realMonomial r.row.rhs (u a)) :
    Contracts (tests.map MonomialTest.row) s (realSupport x) := by
  classical
  let t := realSupport x
  have ht : t ⊆ s := by
    intro i hi
    by_contra hni
    have hzero : (fun a => u a i) =ᶠ[l] (fun _ => 0) := by
      filter_upwards [hs] with a ha
      have hm : i ∉ realSupport (u a) := ha ▸ hni
      simpa using hm
    have hl₀ : Tendsto (fun a => u a i) l (𝓝 0) := tendsto_const_nhds.congr' hzero.symm
    exact (mem_realSupport.mp hi) (tendsto_nhds_unique (hlimit i) hl₀)
  let Z := s \ t
  let J := {k : Fin tests.length // (tests.get k).row.active s}
  let r (j : J) := tests.get j.1
  let d (j : J) (i : I) : ℚ := ((r j).row.lhs i : ℚ) - ((r j).row.rhs i : ℚ)
  let A : Matrix J Z ℚ := fun j i => d j i
  let Ar := (A.map (Rat.castHom ℝ)).mulVecLin
  let v (a : α) (i : Z) := Real.log (u a i)
  have hd (i : Z) : Tendsto (fun a => v a i) l atBot := by
    have hi := Finset.mem_sdiff.mp i.2
    have hx₀ : x i = 0 := by simpa [t] using hi.2
    have hp : Tendsto (fun a => u a i) l (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.2
      refine ⟨hx₀ ▸ hlimit i, ?_⟩
      filter_upwards [hs] with a ha
      have hm : (i : I) ∈ realSupport (u a) := ha.symm ▸ hi.1
      exact mem_realSupport.mp hm
    exact Real.tendsto_log_nhdsNE_zero.comp hp
  have hsplit : ∀ᶠ a in l, ∀ j : J, Ar (v a) j =
      Real.log ((r j).ratio : ℝ) - ∑ i ∈ t, (d j i : ℝ) * Real.log (u a i) := by
    filter_upwards [hs, hlegal] with a ha hq
    intro j
    have ha' : (r j).row.active (realSupport (u a)) := ha.symm ▸ j.2
    have heq := log_equation (r j) (u a) ha' (hq (r j) (List.get_mem _ _))
    have heq' : (∑ i, (d j i : ℝ) * Real.log (u a i)) = Real.log ((r j).ratio : ℝ) := by
      simpa [d] using heq
    have hsum : (∑ i ∈ s, (d j i : ℝ) * Real.log (u a i)) =
        ∑ i, (d j i : ℝ) * Real.log (u a i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hz : (r j).row.lhs i = 0 ∧ (r j).row.rhs i = 0 := j.2 i hi
      simp [d, hz.1, hz.2]
    have hsplit' := Finset.sum_sdiff ht
      (f := fun i => (d j i : ℝ) * Real.log (u a i))
    have hAr : Ar (v a) j = ∑ i ∈ s \ t, (d j i : ℝ) * Real.log (u a i) := by
      change (∑ i : Z, (d j (i : I) : ℝ) * Real.log (u a i)) = _
      exact Finset.sum_coe_sort Z (fun i : I => (d j i : ℝ) * Real.log (u a i))
    rw [hAr]
    linarith
  have hconv : Tendsto (fun a => Ar (v a)) l
      (𝓝 (fun j => Real.log ((r j).ratio : ℝ) - ∑ i ∈ t, (d j i : ℝ) * Real.log (x i))) := by
    apply tendsto_pi_nhds.2
    intro j
    have he : Tendsto
        (fun a => Real.log ((r j).ratio : ℝ) - ∑ i ∈ t, (d j i : ℝ) * Real.log (u a i)) l
        (𝓝 (Real.log ((r j).ratio : ℝ) - ∑ i ∈ t, (d j i : ℝ) * Real.log (x i))) := by
      apply tendsto_const_nhds.sub
      apply tendsto_finset_sum
      intro i hi
      exact tendsto_const_nhds.mul ((Real.continuousAt_log (mem_realSupport.mp hi)).tendsto.comp
        (hlimit i))
    exact he.congr' (hsplit.mono fun a h => (h j).symm)
  let p (j : J) := Real.log ((r j).ratio : ℝ) - ∑ i ∈ t, (d j i : ℝ) * Real.log (x i)
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ a in l, ‖Ar (v a)‖ ≤ C := by
    refine ⟨‖p‖ + 1, by positivity, ?_⟩
    have hn : Tendsto (fun a => ‖Ar (v a)‖) l (𝓝 ‖p‖) := hconv.norm
    exact ((tendsto_order.1 hn).2 _ (by linarith)).mono fun _ ha => ha.le
  obtain ⟨vR, hvR, hposR⟩ := positive_kernel_of_divergence Ar hd hbound
  obtain ⟨wZ, hwZ, hposZ⟩ := positive_integer_kernel A vR hvR hposR
  let w (i : I) := if hi : i ∈ Z then wZ ⟨i, hi⟩ else 0
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    have hz : i ∉ Z := fun h => hi (Finset.mem_sdiff.mp h).1
    simp [w, hz]
  · intro row hrow hactive
    obtain ⟨c, hc, hcrow⟩ := List.mem_map.mp hrow
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    have hk' : (tests.get k).row = row := by
      rw [hk]
      exact hcrow
    let j : J := ⟨k, hk' ▸ hactive⟩
    have hj : (r j).row = row := hk'
    have hwj := congrFun hwZ j
    have hZw : (∑ i, ((row.lhs i : ℚ) - (row.rhs i : ℚ)) * (w i : ℚ)) =
        ∑ i ∈ Z, ((row.lhs i : ℚ) - (row.rhs i : ℚ)) * (w i : ℚ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp [w, hi]
    have hzero : (∑ i, ((row.lhs i : ℚ) - (row.rhs i : ℚ)) * (w i : ℚ)) = 0 := by
      rw [hZw]
      have heq : (∑ i ∈ Z, ((row.lhs i : ℚ) - (row.rhs i : ℚ)) * (w i : ℚ)) =
          ∑ i : Z, ((row.lhs i : ℚ) - (row.rhs i : ℚ)) * (wZ i : ℚ) := by
        rw [← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        intro i _
        simp [w, i.2]
      rw [heq]
      simpa [A, d, hj, Matrix.mulVec, dotProduct] using hwj
    simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at hzero
    exact_mod_cast hzero
  · ext i
    change i ∈ t ↔ i ∈ s.filter (fun i => w i = 0)
    rw [Finset.mem_filter]
    by_cases hi : i ∈ t
    · have hz : i ∉ Z := fun h => (Finset.mem_sdiff.mp h).2 hi
      simp [hi, ht hi, w, hz]
    · by_cases hi' : i ∈ s
      · have hz : i ∈ Z := Finset.mem_sdiff.mpr ⟨hi', hi⟩
        simp [hi, hi', w, hz, (hposZ ⟨i, hz⟩).ne']
      · simp [hi, hi']

end MovingProjection
