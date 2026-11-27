import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The rank-one ratio equation cannot have three roots. This is the
analytic step in the zero-probe finite-ratio criterion. -/

namespace MovingProjection.NoProbeRatios

private theorem exp_chord {x y z a u v : ℝ} (hy : y = u*x + v*z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u+v=1) :
    Real.exp (a*y) ≤ u * Real.exp (a*x) + v * Real.exp (a*z) := by
  rw [show a*y = u*(a*x) + v*(a*z) by rw [hy]; ring]
  simpa only [smul_eq_mul] using convexOn_exp.2 (Set.mem_univ (a*x))
    (Set.mem_univ (a*z)) hu hv hs

private theorem exp_strict_chord {x y z a u v : ℝ} (hy : y = u*x + v*z)
    (h : x ≠ z) (ha : a ≠ 0) (hu : 0 < u) (hv : 0 < v) (hs : u+v=1) :
    Real.exp (a*y) < u * Real.exp (a*x) + v * Real.exp (a*z) := by
  rw [show a*y = u*(a*x) + v*(a*z) by rw [hy]; ring]
  have hne : a*x ≠ a*z := fun he => h (mul_left_cancel₀ ha he)
  simpa only [smul_eq_mul] using strictConvexOn_exp.2 (Set.mem_univ (a*x))
    (Set.mem_univ (a*z)) hne hu hv hs

theorem rank_one_no_three {a b c x y z : ℝ} (hc : 0 < c) (hc' : c < 1)
    (hab : a ≠ 0 ∨ b ≠ 0) (hxy : x < y) (hyz : y < z)
    (hx : c*Real.exp (a*x) + (1-c)*Real.exp (b*x) = 1)
    (hz : c*Real.exp (a*z) + (1-c)*Real.exp (b*z) = 1) :
    c*Real.exp (a*y) + (1-c)*Real.exp (b*y) < 1 := by
  have hzx : 0 < z-x := by linarith
  let u := (z-y)/(z-x)
  let v := (y-x)/(z-x)
  have hu : 0 < u := div_pos (sub_pos.mpr hyz) hzx
  have hv : 0 < v := div_pos (sub_pos.mpr hxy) hzx
  have hs : u+v=1 := by
    dsimp [u,v]
    field_simp
    ring
  have hy : y = u*x+v*z := by
    dsimp [u,v]
    field_simp
    ring
  have h₁ : x ≠ z := (hxy.trans hyz).ne
  have hsum : u*(c*Real.exp (a*x)+(1-c)*Real.exp (b*x)) +
      v*(c*Real.exp (a*z)+(1-c)*Real.exp (b*z)) = 1 := by
    rw [hx,hz, mul_one, mul_one, hs]
  have he : c*(u*Real.exp (a*x)+v*Real.exp (a*z)) +
      (1-c)*(u*Real.exp (b*x)+v*Real.exp (b*z)) = 1 := by
    calc
      _ = u*(c*Real.exp (a*x)+(1-c)*Real.exp (b*x)) +
        v*(c*Real.exp (a*z)+(1-c)*Real.exp (b*z)) := by ring
      _ = 1 := hsum
  calc
    _ < c*(u*Real.exp (a*x)+v*Real.exp (a*z)) +
        (1-c)*(u*Real.exp (b*x)+v*Real.exp (b*z)) := ?_
    _ = 1 := he
  rcases hab with ha | hb
  · have hl := mul_lt_mul_of_pos_left (exp_strict_chord hy h₁ ha hu hv hs) hc
    have hr := mul_le_mul_of_nonneg_left (exp_chord (a := b) hy hu.le hv.le hs)
      (sub_nonneg.mpr hc'.le)
    exact add_lt_add_of_lt_of_le hl hr
  · have hl := mul_le_mul_of_nonneg_left (exp_chord (a := a) hy hu.le hv.le hs) hc.le
    have hr := mul_lt_mul_of_pos_left (exp_strict_chord hy h₁ hb hu hv hs) (sub_pos.mpr hc')
    exact add_lt_add_of_le_of_lt hl hr

end MovingProjection.NoProbeRatios
