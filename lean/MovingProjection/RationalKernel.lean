import MovingProjection.Closure
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Ring

/-! Strict real kernel feasibility is inherited by a rational matrix. -/

namespace MovingProjection

open Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

private theorem generalizedInverse (A : Matrix J I ℚ) :
    ∃ B : Matrix I J ℚ, A * B * A = A := by
  classical
  let f := A.toLin'
  obtain ⟨c, hcomp⟩ := Submodule.exists_isCompl f.range
  let p := f.range.linearProjOfIsCompl c hcomp
  obtain ⟨sectionMap, hsec⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  refine ⟨(sectionMap.comp p).toMatrix', ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  change f (sectionMap (p (f x))) = f x
  have hp : p (f x) = f.rangeRestrict x :=
    Submodule.linearProjOfIsCompl_apply_left hcomp (f.rangeRestrict x)
  rw [hp]
  have ht : f.rangeRestrict (sectionMap (f.rangeRestrict x)) = f.rangeRestrict x :=
    LinearMap.congr_fun hsec (f.rangeRestrict x)
  exact congrArg Subtype.val ht

/-- Project rational approximants along a rational complement so that they
satisfy the same homogeneous equations exactly. -/
theorem positive_rational_kernel (A : Matrix J I ℚ) (w : I → ℝ)
    (hw : (A.map (Rat.castHom ℝ)) *ᵥ w = 0) (hpos : ∀ i, 0 < w i) :
    ∃ q : I → ℚ, A *ᵥ q = 0 ∧ ∀ i, 0 < q i := by
  classical
  obtain ⟨B, hABA⟩ := generalizedInverse A
  let P : Matrix I I ℚ := 1 - B*A
  have hAP : A * P = 0 := by
    change A * (1 - B*A) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hABA, sub_self]
  let PR := P.map (Rat.castHom ℝ)
  have hPR : PR = 1 - B.map (Rat.castHom ℝ) * A.map (Rat.castHom ℝ) := by
    ext i j
    simp [PR, P, Matrix.mul_apply, Matrix.one_apply]
    split <;> simp
  have hfix : PR *ᵥ w = w := by
    rw [hPR, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero, sub_zero]
  have hc : Continuous fun x : I → ℝ => PR *ᵥ x :=
    PR.mulVecLin.continuous_of_finiteDimensional
  let U : Set (I → ℝ) := {x | ∀ i, 0 < (PR *ᵥ x) i}
  have hU : IsOpen U := by
    change IsOpen {x | ∀ i, 0 < (PR *ᵥ x) i}
    rw [show {x | ∀ i, 0 < (PR *ᵥ x) i} = ⋂ i, {x | 0 < (PR *ᵥ x) i} by ext; simp]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const ((continuous_apply i).comp hc))
  have hd : DenseRange (fun q : I → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.isDenseEmbedding_coe_real.dense)
  obtain ⟨v, hv⟩ := hd.exists_mem_open hU ⟨w, by simpa [U, hfix] using hpos⟩
  refine ⟨P *ᵥ v, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, hAP, Matrix.zero_mulVec]
  · intro i
    have hi := (show ∀ i, 0 < (PR *ᵥ fun j => (v j : ℝ)) i from hv) i
    have he := RingHom.map_mulVec (Rat.castHom ℝ) P v i
    change ((P *ᵥ v) i : ℝ) = (PR *ᵥ fun j => (v j : ℝ)) i at he
    rw [← he] at hi
    exact_mod_cast hi

theorem positive_integer_kernel (A : Matrix J I ℚ) (x : I → ℝ)
    (hx : (A.map (Rat.castHom ℝ)) *ᵥ x = 0) (hpos : ∀ i, 0 < x i) :
    ∃ w : I → ℕ, A *ᵥ (fun i => (w i : ℚ)) = 0 ∧ ∀ i, 0 < w i := by
  classical
  obtain ⟨q, hker, hq⟩ := positive_rational_kernel A x hx hpos
  let N : ℕ := ∏ i, (q i).den
  let w (i : I) : ℕ := (q i).num.toNat * ∏ j ∈ Finset.univ.erase i, (q j).den
  have hw (i : I) : (w i : ℚ) = (N : ℚ) * q i := by
    have hnum := Int.toNat_of_nonneg (Rat.num_pos.mpr (hq i)).le
    have hnumCast : ((q i).num.toNat : ℚ) = (q i).num := by
      exact_mod_cast hnum
    have hd : ((q i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
    have hn := (div_eq_iff hd).mp (q i).num_div_den
    have hp : (N : ℚ) = ((∏ j ∈ Finset.univ.erase i, (q j).den : ℕ) : ℚ) * (q i).den := by
      unfold N
      exact_mod_cast (Finset.prod_erase_mul Finset.univ (fun j => (q j).den) (Finset.mem_univ i)).symm
    simp only [w, Nat.cast_mul, hnumCast, hp, hn]
    ring
  refine ⟨w, ?_, ?_⟩
  · have heq : (fun i => (w i : ℚ)) = (N : ℚ) • q := funext hw
    rw [heq, Matrix.mulVec_smul, hker, smul_zero]
  · intro i
    have hN : 0 < N := by
      unfold N
      exact Finset.prod_pos fun j _ => (q j).pos
    have hh : (0 : ℚ) < (w i : ℚ) := by
      rw [hw]
      exact mul_pos (Nat.cast_pos.mpr hN) (hq i)
    exact_mod_cast hh

end MovingProjection
