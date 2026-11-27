import MovingProjection.CoreCertificate
import MovingProjection.RationalKernel
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-! Every irreducible support has an integer strict dual, so the executable
checker accepts some certificate at every input. -/

namespace MovingProjection.CoreCertificate

open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

private def entry (rows : List (ExponentRow I)) (s : Finset I)
    (k : Fin rows.length) (i : I) : ℤ :=
  if activeCheck rows[k] s then (rows[k].lhs i : ℤ) - rows[k].rhs i else 0

private theorem no_zero_in_hull (rows : List (ExponentRow I)) (s : Finset I)
    (hirr : ∀ t, Contracts rows s t → t = s) :
    (0 : Fin rows.length → ℝ) ∉ convexHull ℝ (Set.range
      (fun i : s => fun k => (entry rows s k i : ℝ))) := by
  classical
  let column (i : s) (k : Fin rows.length) : ℝ := entry rows s k i
  change (0 : Fin rows.length → ℝ) ∉ convexHull ℝ (Set.range column)
  rw [convexHull_range_eq_exists_affineCombination]
  rintro ⟨T, w, hw, hsum, hcomb⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hcomb
  let U := T.filter (fun j => 0 < w j)
  have hU : U.Nonempty := by
    by_contra hn
    have hz : ∀ i ∈ T, w i = 0 := by
      intro i hi
      apply le_antisymm _ (hw i hi)
      exact le_of_not_gt (fun hh => hn ⟨i, Finset.mem_filter.mpr ⟨hi, hh⟩⟩)
    have he := Finset.sum_eq_zero hz
    linarith
  let A : Matrix (Fin rows.length) U ℚ := fun k i => entry rows s k i.val.val
  have hker : (A.map (Rat.castHom ℝ)) *ᵥ (fun i : U => w i) = 0 := by
    funext k
    have h := congrFun hcomb k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h
    change (∑ i : U, ((A k i : ℚ) : ℝ) * w i) = 0
    simp only [A, Rat.cast_intCast, mul_comm (_ : ℝ) (w _)]
    change (∑ i : U, w (i : s) * column (i : s) k) = 0
    rw [Finset.sum_coe_sort U (fun i => w i * column i k)]
    calc
      _ = ∑ i ∈ T, w i * column i k := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hn
        have hz : w i = 0 := le_antisymm
          (le_of_not_gt (fun hh => hn (Finset.mem_filter.mpr ⟨hi, hh⟩))) (hw i hi)
        simp [hz]
      _ = 0 := h
  obtain ⟨z, hz, hzpos⟩ :=
    positive_integer_kernel A (fun i : U => w i) hker
      (fun i => (Finset.mem_filter.mp i.property).2)
  let extend (i : I) : ℕ := ∑ j : U, if j.val.val = i then z j else 0
  have hout : ∀ i ∉ s, extend i = 0 := by
    intro i hi
    unfold extend
    apply Finset.sum_eq_zero
    intro j _
    have hne : j.val.val ≠ i := fun he => hi (he ▸ j.val.property)
    simp [hne]
  have hbal (k : Fin rows.length) : (∑ i, entry rows s k i * (extend i : ℤ)) = 0 := by
    have he := congrFun hz k
    change (∑ j : U, A k j * (z j : ℚ)) = 0 at he
    have he' : ∑ j : U, entry rows s k j.val.val * (z j : ℤ) = 0 := by
      unfold A at he
      exact_mod_cast he
    unfold extend
    simp only [Nat.cast_sum, Finset.mul_sum, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simpa using he'
  have hd : Damping rows s extend := by
    refine ⟨hout, ?_⟩
    intro row hr ha
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
    change rows[k] = row at hk
    have hc : activeCheck rows[k] s = true := activeCheck_eq_true.mpr (hk.symm ▸ ha)
    have hb := hbal k
    simp only [entry, hc, if_true, sub_mul, Finset.sum_sub_distrib] at hb
    rw [hk] at hb
    exact_mod_cast sub_eq_zero.mp hb
  obtain ⟨u, hu⟩ := hU
  let j : U := ⟨u, hu⟩
  have hj : 0 < extend u.val := by
    unfold extend
    have he : j.val.val = u.val := rfl
    exact (by simpa only [he, if_true] using hzpos j : 0 < (if j.val.val = u.val then z j else 0)).trans_le
      (Finset.single_le_sum (f := fun l : U => if l.val.val = u.val then z l else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  have hr := hirr _ ⟨extend, hd, rfl⟩
  have hm : u.val ∈ s.filter (fun i => extend i = 0) := hr.symm ▸ u.property
  exact (ne_of_gt hj) (Finset.mem_filter.mp hm).2

private theorem exists_strict_dual (rows : List (ExponentRow I)) (s : Finset I)
    (hirr : ∀ t, Contracts rows s t → t = s) :
    ∃ dual : Fin rows.length → ℤ, terminalCheck rows s dual = true := by
  classical
  let col (i : s) (k : Fin rows.length) : ℝ := entry rows s k i
  let K := convexHull ℝ (Set.range col)
  have hK : IsClosed K := (Set.finite_range col).isClosed_convexHull
  obtain ⟨f, u, hu, hf⟩ :=
    geometric_hahn_banach_point_closed (convex_convexHull ℝ (Set.range col)) hK
      (no_zero_in_hull rows s hirr)
  let a (k : Fin rows.length) : ℝ := f (Pi.single k 1)
  have ha (i : s) : 0 < ∑ k, a k * col i k := by
    let e (k : Fin rows.length) : Fin rows.length → ℝ := Pi.single k 1
    have he : (∑ k, col i k • e k) = col i := by
      ext j
      simp only [e, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx := hf (col i) (subset_convexHull ℝ _ (Set.mem_range_self i))
    have hpos : 0 < f (col i) := (by simpa only [map_zero] using hu : 0 < u).trans hx
    rw [← he, map_sum] at hpos
    simpa only [a, e, map_smul, smul_eq_mul, mul_comm] using hpos
  let good : Set (Fin rows.length → ℝ) := {x | ∀ i : s, 0 < ∑ k, x k * col i k}
  have hopen : IsOpen good := by
    change IsOpen {x : Fin rows.length → ℝ | ∀ i : s, 0 < ∑ k, x k * col i k}
    rw [show {x : Fin rows.length → ℝ | ∀ i : s, 0 < ∑ k, x k * col i k} =
      ⋂ i : s, {x : Fin rows.length → ℝ | 0 < ∑ k, x k * col i k} by ext; simp]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const
      (continuous_finset_sum _ (fun k _ => (continuous_apply k).mul continuous_const))
  have hdense : DenseRange (fun v : Fin rows.length → ℚ => fun k => (v k : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.isDenseEmbedding_coe_real.dense)
  obtain ⟨v, hv⟩ := hdense.exists_mem_open hopen ⟨a, ha⟩
  let d : ℕ := ∏ k, (v k).den
  have hd : 0 < d := Finset.prod_pos (fun k _ => (v k).pos)
  let dual (k : Fin rows.length) : ℤ := (v k).num * (↑(∏ j ∈ Finset.univ.erase k, (v j).den) : ℤ)
  have hdual (k : Fin rows.length) : (dual k : ℚ) = (d : ℚ) * v k := by
    have h₂ : (d : ℚ) = (↑(∏ j ∈ Finset.univ.erase k, (v j).den) : ℚ) * (v k).den := by
      exact_mod_cast (Finset.prod_erase_mul Finset.univ (fun j => (v j).den) (Finset.mem_univ k)).symm
    have hn := (div_eq_iff (by exact_mod_cast (v k).den_ne_zero)).mp (v k).num_div_den
    simp only [dual, Int.cast_mul, Int.cast_natCast, h₂, hn]
    ring
  refine ⟨dual, decide_eq_true ?_⟩
  intro i hi
  have hpos : (0 : ℚ) < ∑ k, v k * (entry rows s k i : ℚ) := by
    have hh := (show ∀ j : s, 0 < ∑ k, (v k : ℝ) * col j k from hv) ⟨i, hi⟩
    unfold col at hh
    exact_mod_cast hh
  have he : (0 : ℚ) < ∑ k, (dual k : ℚ) * (entry rows s k i : ℚ) := by
    simp_rw [hdual, mul_assoc, ← Finset.mul_sum]
    exact mul_pos (by exact_mod_cast hd) hpos
  unfold dualCoordinate
  have hz : (0 : ℤ) < ∑ k, dual k * entry rows s k i := by exact_mod_cast he
  simpa only [entry, mul_ite, mul_zero] using hz

theorem checkCore_complete_short (rows : List (ExponentRow I)) (s : Finset I) :
    ∃ witness : Witness rows, checkCore rows s witness = some (core rows s) ∧
      witness.steps.length + (core rows s).card ≤ s.card := by
  let c := core rows s
  have hc := isCore_core rows s
  obtain ⟨steps, hsteps, hlength⟩ := replay_complete_short hc.1
  have hirr (t : Finset I) (ht : Contracts rows c t) : t = c :=
    Finset.Subset.antisymm ht.subset (hc.2 t (hc.1.tail ht))
  obtain ⟨μ, hμ⟩ := exists_strict_dual rows c hirr
  exact ⟨⟨steps, μ⟩, by simp [checkCore, hsteps, c, hμ], hlength⟩

theorem checkCore_complete (rows : List (ExponentRow I)) (s : Finset I) :
    ∃ witness : Witness rows, checkCore rows s witness = some (core rows s) := by
  obtain ⟨witness, hcheck, _⟩ := checkCore_complete_short rows s
  exact ⟨witness, hcheck⟩

theorem checkPair_complete (rows : List (ExponentRow I)) (x y : I → ℚ) :
    ∃ left right : Witness rows, ∃ verdict, checkPair rows x y left right = some verdict := by
  obtain ⟨left, hl⟩ := checkCore_complete rows (support x)
  obtain ⟨right, hr⟩ := checkCore_complete rows (support y)
  refine ⟨left, right, decide (core rows (support x) = core rows (support y) ∧
    ∀ i, i ∈ core rows (support x) → (0 < x i ↔ 0 < y i)), ?_⟩
  simp only [checkPair, hl, hr]

theorem native_certificate_exists
    {M X R Γ Δ : Type*} [Fintype M] [Fintype X] [Fintype R] [Fintype Γ] [Fintype Δ]
    [DecidableEq M] [Nonempty M] [Nonempty X] [Nonempty R]
    (D : NativeExperiments M I X R Γ Δ) {n : ℕ} (a b : D.protocol.State n) :
    let rows := (D.protocol.fiber a.profile).spectralChecks.map MonomialTest.row
    ∃ left right : Witness rows, ∃ verdict,
      checkPair rows a.law.spectrum b.law.spectrum left right = some verdict ∧
        (D.protocol.Factorable a b ↔ a.profile ≤ b.profile ∧ verdict = true) := by
  dsimp only
  obtain ⟨left, right, verdict, hv⟩ :=
    checkPair_complete ((D.protocol.fiber a.profile).spectralChecks.map MonomialTest.row)
      a.law.spectrum b.law.spectrum
  exact ⟨left, right, verdict, hv, native_certificate D a b hv⟩

end MovingProjection.CoreCertificate
