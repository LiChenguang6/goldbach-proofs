import PEqualNP.Weyl.Trig

/-!
# Layer 1b: distance-to-integer lower bound for `‖E α - 1‖`

`|sin (π u)| ≥ u` on `[0, 1/2]`, hence `‖E α - 1‖ ≥ 2 |α|` when `|α| ≤ 1/2`.
The constant `2` (rather than the optimal `4`) is deliberate: every later
estimate only needs *some* explicit positive constant.
-/

namespace PEqualNP.Weyl

noncomputable section

lemma sin_pi_ge_of_le_half {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    u ≤ Real.sin (Real.pi * u) := by
  have hpi0 : (0 : ℝ) ≤ Real.pi * u := by positivity
  have hcube := Real.sin_ge_sub_cube hpi0
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have hpi3 : Real.pi ^ 3 ≤ 31.26 := by
    have hlt : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
    have hpos : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    nlinarith [sq_nonneg Real.pi, sq_nonneg (Real.pi - 3.15), sq_nonneg (Real.pi - 3.14)]
  have hcube_le : Real.pi ^ 3 * u ^ 2 / 6 ≤ 1.31 := by
    have h1 : Real.pi ^ 3 * u ^ 2 ≤ 31.26 * (1 / 4) := by
      exact mul_le_mul hpi3 hu2 (by positivity) (by positivity)
    linarith
  have hcoef : 1 ≤ Real.pi - Real.pi ^ 3 * u ^ 2 / 6 := by
    have hgt : 3.14 < Real.pi := Real.pi_gt_d2
    linarith
  have hmain : u ≤ Real.pi * u - (Real.pi * u) ^ 3 / 6 := by
    have hsplit : Real.pi * u - (Real.pi * u) ^ 3 / 6 =
        u * (Real.pi - Real.pi ^ 3 * u ^ 2 / 6) := by ring
    rw [hsplit]
    calc u = u * 1 := (mul_one u).symm
      _ ≤ u * (Real.pi - Real.pi ^ 3 * u ^ 2 / 6) := by
          exact mul_le_mul_of_nonneg_left hcoef hu0
  linarith

/-- `|sin (π α)| = sin (π |α|)` when `|α| ≤ 1/2`. -/
lemma abs_sin_pi {α : ℝ} (h : |α| ≤ 1 / 2) :
    |Real.sin (Real.pi * α)| = Real.sin (Real.pi * |α|) := by
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → 0 ≤ Real.sin (Real.pi * x) := by
    intro x hx0 hx
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos, hx]
  rcases le_or_gt 0 α with hα | hα
  · have hle : α ≤ 1 / 2 := by
      rw [abs_of_nonneg hα] at h
      exact h
    rw [abs_of_nonneg hα, abs_of_nonneg (key α hα hle)]
  · have hle : -α ≤ 1 / 2 := by
      rw [abs_of_neg hα] at h
      exact h
    have hsin : Real.sin (Real.pi * α) = -Real.sin (Real.pi * (-α)) := by
      rw [show Real.pi * α = -(Real.pi * (-α)) by ring, Real.sin_neg]
    rw [abs_of_neg hα, hsin, abs_neg, abs_of_nonneg (key (-α) (by linarith) hle)]

/-- Distance form: `‖E α - 1‖ ≥ 2 |α|` for `|α| ≤ 1/2`. -/
lemma norm_E_sub_one_ge {α : ℝ} (h : |α| ≤ 1 / 2) :
    2 * |α| ≤ ‖E α - 1‖ := by
  rw [norm_E_sub_one, abs_sin_pi h]
  have h0 : (0 : ℝ) ≤ |α| := abs_nonneg α
  have := sin_pi_ge_of_le_half h0 h
  linarith

end

end PEqualNP.Weyl
