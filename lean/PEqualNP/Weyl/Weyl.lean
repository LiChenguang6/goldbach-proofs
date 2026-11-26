import PEqualNP.Weyl.Differ

/-!
# Layer 3a: Weyl differencing for the quadratic phase `E (α n²)`

Specializing the general differencing bound to `z n = E (α n²)`, where all
coefficients have modulus one, yields

`‖∑_{n<N} E (α n²)‖² ≤ N + 2 ∑_{h=1}^{N-1} ‖∑_{k<N-h} E (2αhk + αh²)‖`.
-/

namespace PEqualNP.Weyl

open Finset

noncomputable section

lemma norm_sum_E_add_const {c d : ℝ} (N : ℕ) :
    ‖∑ k ∈ Finset.range N, E ((k : ℝ) * c + d)‖
      = ‖∑ k ∈ Finset.range N, E ((k : ℝ) * c)‖ := by
  have h : (∑ k ∈ Finset.range N, E ((k : ℝ) * c + d))
      = E d * ∑ k ∈ Finset.range N, E ((k : ℝ) * c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [E_add, mul_comm]
  rw [h, norm_mul, norm_E]
  simp

lemma norm_sum_E_quad_inner (α : ℝ) (h M : ℕ)
    (hc0 : 2 * α * (h : ℝ) ≠ 0) (hc : |2 * α * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ k ∈ Finset.range M, E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2)‖
      ≤ min (M : ℝ) (1 / |2 * α * (h : ℝ)|) := by
  have hshift : (∑ k ∈ Finset.range M,
        E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2))
      = ∑ k ∈ Finset.range M, E ((k : ℝ) * (2 * α * (h : ℝ)) + α * (h : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  rw [hshift, norm_sum_E_add_const]
  exact norm_sum_E_le_min hc0 hc M

lemma weyl_quad (α : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, E (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
          ‖∑ k ∈ Finset.range (N - h),
            E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2)‖ := by
  have hmain := differ_bound N (fun n => E (α * (n : ℝ) ^ 2))
  have hdiag : (∑ n ∈ Finset.range N, ‖E (α * (n : ℝ) ^ 2)‖ ^ 2) = (N : ℝ) := by
    have h1 : ∀ n ∈ Finset.range N, ‖E (α * (n : ℝ) ^ 2)‖ ^ 2 = (1 : ℝ) := by
      intro n _
      rw [norm_E]
      norm_num
    rw [Finset.sum_congr rfl h1]
    simp
  rw [hdiag] at hmain
  have hinner : (∑ h ∈ Finset.Icc 1 (N - 1),
        ‖∑ k ∈ Finset.range (N - h),
          E (α * (((k + h : ℕ) : ℝ)) ^ 2) * star (E (α * (k : ℝ) ^ 2))‖)
      = ∑ h ∈ Finset.Icc 1 (N - 1),
          ‖∑ k ∈ Finset.range (N - h),
            E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2)‖ := by
    apply Finset.sum_congr rfl
    intro h _
    have hk : (∑ k ∈ Finset.range (N - h),
          E (α * (((k + h : ℕ) : ℝ)) ^ 2) * star (E (α * (k : ℝ) ^ 2)))
        = ∑ k ∈ Finset.range (N - h),
            E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2) :=
      Finset.sum_congr rfl (fun k _ => E_quad_shift α k h)
    rw [hk]
  rw [hinner] at hmain
  exact hmain

lemma weyl_inner_bound (α : ℝ) (N h : ℕ)
    (h0 : 2 * α * (h : ℝ) ≠ 0) (h1 : |2 * α * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ k ∈ Finset.range (N - h),
        E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2)‖
      ≤ min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|) := by
  have hrew : (∑ k ∈ Finset.range (N - h),
        E (2 * α * (h : ℝ) * (k : ℝ) + α * (h : ℝ) ^ 2))
      = ∑ k ∈ Finset.range (N - h),
          E ((k : ℝ) * (2 * α * (h : ℝ)) + α * (h : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast
    ring
  rw [hrew, norm_sum_E_add_const (c := 2 * α * (h : ℝ)) (d := α * (h : ℝ) ^ 2)]
  exact norm_sum_E_le_min h0 h1 (N - h)

lemma weyl_quad_bound (α : ℝ) (N : ℕ)
    (hzero : ∀ h ∈ Finset.Icc 1 (N - 1), 2 * α * (h : ℝ) ≠ 0)
    (hsmall : ∀ h ∈ Finset.Icc 1 (N - 1), |2 * α * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N, E (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
          min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|) := by
  refine le_trans (weyl_quad α N) ?_
  gcongr
  exact weyl_inner_bound α N _ (hzero _ ‹_›) (hsmall _ ‹_›)

lemma weyl_quad_crude (α : ℝ) (N : ℕ) (hα : α ≠ 0) (hN : 1 ≤ N)
    (hsmall : ∀ h ∈ Finset.Icc 1 (N - 1), |2 * α * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N, E (α * (n : ℝ) ^ 2)‖ ^ 2
      ≤ (N : ℝ) + 2 * (N : ℝ) * min (N : ℝ) (1 / (2 * |α|)) := by
  have hzero : ∀ h ∈ Finset.Icc 1 (N - 1), 2 * α * (h : ℝ) ≠ 0 := by
    intro h hh
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by
      have := (Finset.mem_Icc.mp hh).1
      exact_mod_cast this
    exact mul_ne_zero (mul_ne_zero (by norm_num) hα)
      (ne_of_gt (lt_of_lt_of_le (by norm_num) h1))
  have hterm : ∀ h ∈ Finset.Icc 1 (N - 1),
      min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|) ≤ min (N : ℝ) (1 / (2 * |α|)) := by
    intro h hh
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by
      have := (Finset.mem_Icc.mp hh).1
      exact_mod_cast this
    have hNh : ((N - h : ℕ) : ℝ) ≤ (N : ℝ) := by
      have hle : N - h ≤ N := Nat.sub_le N h
      exact_mod_cast hle
    have hden : 2 * |α| ≤ |2 * α * (h : ℝ)| := by
      have hcast : |(h : ℝ)| = (h : ℝ) := abs_of_nonneg (by positivity)
      calc |2 * α * (h : ℝ)| = |2 * α| * |(h : ℝ)| := by rw [abs_mul]
        _ = (2 * |α|) * (h : ℝ) := by rw [abs_mul, hcast]; norm_num
        _ ≥ 2 * |α| * 1 := by nlinarith [h1, abs_nonneg α]
        _ = 2 * |α| := by ring
    have hp : (0 : ℝ) < 2 * |α| := by
      have hpos : 0 < |α| := abs_pos.mpr hα
      nlinarith
    have hle : 1 / |2 * α * (h : ℝ)| ≤ 1 / (2 * |α|) :=
      one_div_le_one_div_of_le hp hden
    exact min_le_min hNh hle
  have hsub : Finset.Icc 1 (N - 1) ⊆ Finset.range N := by
    intro h hh
    have hle : h ≤ N - 1 := (Finset.mem_Icc.mp hh).2
    have hlt : h < N := by omega
    exact Finset.mem_range.mpr hlt
  have hM : (0 : ℝ) ≤ min (N : ℝ) (1 / (2 * |α|)) := by positivity
  have hsumle : (∑ h ∈ Finset.Icc 1 (N - 1),
        min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|))
      ≤ (N : ℝ) * min (N : ℝ) (1 / (2 * |α|)) := by
    have h1 := Finset.sum_le_card_nsmul (Finset.Icc 1 (N - 1))
      (fun h => min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|))
      (min (N : ℝ) (1 / (2 * |α|))) hterm
    have h2 : ((Finset.Icc 1 (N - 1)).card : ℝ) ≤ (N : ℝ) := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_range] at hc
      exact_mod_cast hc
    calc (∑ h ∈ Finset.Icc 1 (N - 1), min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|))
        ≤ ((Finset.Icc 1 (N - 1)).card : ℝ) * min (N : ℝ) (1 / (2 * |α|)) := by
          rw [nsmul_eq_mul] at h1
          exact h1
      _ ≤ (N : ℝ) * min (N : ℝ) (1 / (2 * |α|)) :=
          mul_le_mul_of_nonneg_right h2 hM
  have h2 : 2 * (∑ h ∈ Finset.Icc 1 (N - 1),
        min ((N - h : ℕ) : ℝ) (1 / |2 * α * (h : ℝ)|))
      ≤ 2 * ((N : ℝ) * min (N : ℝ) (1 / (2 * |α|))) :=
    mul_le_mul_of_nonneg_left hsumle (by norm_num)
  linarith [weyl_quad_bound α N hzero hsmall, h2]

end

end PEqualNP.Weyl
