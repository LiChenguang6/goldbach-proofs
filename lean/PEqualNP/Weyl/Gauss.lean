import PEqualNP.Weyl.Period
import PEqualNP.Weyl.Shift
import PEqualNP.Weyl.Differ

/-!
# Layer 3e: the residue (Gauss) sum and its difference phase

After `Weyl/Period.lean` reduces the quadratic sum to the residue sum
`G a = ∑_{r<q} E (a r² / q)`, the modulus square of `G a` expands into the
difference phase `E (a (r² - s²) / q)`.  Orthogonality over `a` then collapses
the `a`-sum, which is the standard route to the second moment of Gauss sums.

All statements use the canonical casts `((r ^ 2 : ℕ) : ℝ)` and the grouped
quotient `(· - ·) / q`, so the exponent matches `sum_E_div_sub` syntactically.
-/

set_option maxHeartbeats 400000

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- Expansion of the squared modulus of the residue sum over its two indices. -/
lemma normSq_gauss_sum {q : ℕ} (a : ℕ) :
    Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)))
      = ∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
          (E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
            * star (E ((a : ℝ) * ((s : ℝ)) ^ 2 / (q : ℝ)))).re :=
  normSq_sum_range q

/-- A product of two conjugate phases is the phase of the difference (canonical casts). -/
lemma gauss_pair_phase {q : ℕ} (hq : 0 < q) (a r s : ℕ) :
    (E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
        * star (E ((a : ℝ) * ((s : ℝ)) ^ 2 / (q : ℝ))))
      = E ((a : ℝ) * (((((r ^ 2 : ℕ) : ℝ)) - (((s ^ 2 : ℕ) : ℝ))) / (q : ℝ))) := by
  rw [E_mul_conj]
  congr 1
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  push_cast
  field_simp
  try ring

/-- Second moment of the residue sums: the `a`-average is `q` times the number of
resonant pairs `(r, s)` with `r² ≡ s² (mod q)`. -/
lemma gauss_second_moment {q : ℕ} (hq : 0 < q) :
    ∑ a ∈ Finset.range q,
        Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)))
      = ∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
          if (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)) then (q : ℝ) else 0 := by
  have h1 : ∀ a ∈ Finset.range q,
      Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)))
        = ∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
            (E ((a : ℝ) * (((((r ^ 2 : ℕ) : ℝ)) - (((s ^ 2 : ℕ) : ℝ))) / (q : ℝ)))).re := by
    intro a _
    rw [normSq_gauss_sum a]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [gauss_pair_phase hq a r s]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Complex.re_sum]
  rw [sum_E_div_sub q hq (r ^ 2) (s ^ 2)]
  by_cases hd : (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ))
  · rw [if_pos hd, if_pos hd]
    simp
  · rw [if_neg hd, if_neg hd]
    simp

/-- Block assembly: a bound for the residue (Gauss) sum propagates to the full
block `n < q * M` with a factor `M`, since the block factors exactly through it. -/
lemma norm_sum_quad_block {q : ℕ} (hq : 0 < q) (a M : ℕ) {B : ℝ}
    (hG : ‖∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))‖ ≤ B) :
    ‖∑ n ∈ Finset.range (q * M), E ((a : ℝ) * ((n : ℝ)) ^ 2 / (q : ℝ))‖
      ≤ (M : ℝ) * B := by
  rw [sum_quad_block hq a M, norm_mul]
  have hM : ‖((M : ℕ) : ℂ)‖ = (M : ℝ) := by simp
  rw [hM]
  exact mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg M)

/-- Pigeonhole for the residue sums: if the total second moment is at most
`q * C`, then some residue `a < q` already has `‖G a‖² ≤ C`. -/
lemma exists_normSq_gauss_le {q : ℕ} (hq : 0 < q) {C : ℝ}
    (hC : (∑ a ∈ Finset.range q,
        Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))))
      ≤ (q : ℝ) * C) :
    ∃ a ∈ Finset.range q,
      Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))) ≤ C := by
  by_contra h
  push_neg at h
  have hne : (Finset.range q).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.pos_iff_ne_zero.mp hq)
  have hsum : (∑ a ∈ Finset.range q, C) = (q : ℝ) * C := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hlt : (q : ℝ) * C
      < ∑ a ∈ Finset.range q,
          Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))) := by
    rw [← hsum]
    exact Finset.sum_lt_sum (fun a ha => le_of_lt (h a ha))
      (by obtain ⟨a, ha⟩ := hne; exact ⟨a, ha, h a ha⟩)
  linarith

/-- From a bound on the squared modulus to a bound on the modulus. -/
lemma norm_le_sqrt_of_normSq_le {z : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : Complex.normSq z ≤ C) : ‖z‖ ≤ Real.sqrt C := by
  have h1 : ‖z‖ ^ 2 ≤ C := by
    rw [← Complex.normSq_eq_norm_sq]
    exact h
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt h1

end

end PEqualNP.Weyl
