import PEqualNP.Weyl.Distance

/-!
# Layer 1c: the linear minor-arc bound in `min` form

`‖∑_{k<N} E (kα)‖ ≤ min N (1/|α|)` for `α ≠ 0`, `|α| ≤ 1/2`.
-/

namespace PEqualNP.Weyl

noncomputable section

lemma norm_sum_E_le_nat (N : ℕ) (α : ℝ) :
    ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖ ≤ (N : ℝ) := by
  calc ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖
      ≤ ∑ k ∈ Finset.range N, ‖E ((k : ℝ) * α)‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp [norm_E]

lemma E_ne_one {α : ℝ} (h0 : α ≠ 0) (h : |α| ≤ 1 / 2) : E α ≠ 1 := by
  intro hE
  have hzero : ‖E α - 1‖ = 0 := by rw [hE]; simp
  rw [norm_E_sub_one] at hzero
  have habs : 0 < |α| := abs_pos.mpr h0
  have hle : |α| ≤ Real.sin (Real.pi * |α|) := sin_pi_ge_of_le_half (le_of_lt habs) h
  have hpos : 0 < Real.sin (Real.pi * |α|) := lt_of_lt_of_le habs hle
  have heq : |Real.sin (Real.pi * α)| = Real.sin (Real.pi * |α|) := abs_sin_pi h
  rw [heq] at hzero
  linarith

lemma norm_sum_E_le_inv {α : ℝ} (h0 : α ≠ 0) (h : |α| ≤ 1 / 2) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖ ≤ 1 / |α| := by
  have hne : E α ≠ 1 := E_ne_one h0 h
  have habs : 0 < |α| := abs_pos.mpr h0
  have heq : |Real.sin (Real.pi * α)| = Real.sin (Real.pi * |α|) := abs_sin_pi h
  have hsin_ge : |α| ≤ |Real.sin (Real.pi * α)| := by
    rw [heq]
    exact sin_pi_ge_of_le_half (le_of_lt habs) h
  have hsin_pos : 0 < |Real.sin (Real.pi * α)| := lt_of_lt_of_le habs hsin_ge
  have hsne : |Real.sin (Real.pi * α)| ≠ 0 := ne_of_gt hsin_pos
  calc ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖
      ≤ 2 / ‖E α - 1‖ := norm_geom_le α N hne
    _ = 2 / (2 * |Real.sin (Real.pi * α)|) := by rw [norm_E_sub_one]
    _ = 1 / |Real.sin (Real.pi * α)| := by field_simp
    _ ≤ 1 / |α| := one_div_le_one_div_of_le habs hsin_ge

lemma norm_sum_E_le_min {α : ℝ} (h0 : α ≠ 0) (h : |α| ≤ 1 / 2) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖ ≤ min (N : ℝ) (1 / |α|) := by
  rw [le_min_iff]
  exact ⟨norm_sum_E_le_nat N α, norm_sum_E_le_inv h0 h N⟩

end

end PEqualNP.Weyl
