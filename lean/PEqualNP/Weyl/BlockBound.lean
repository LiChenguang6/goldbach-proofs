import PEqualNP.Weyl.Alpha
import PEqualNP.Weyl.Affine

/-!
# Layer 4c: block estimate for the phase `α = a/q + β`

Combining the residue decomposition with the affine Weyl bound for the inner
sums, the quadratic sum over a block of `M` complete residue systems satisfies

`‖∑_{n<qM} E (α n²)‖² ≤ q² (M + 2 ∑_h min (M - h, 1/(2 |β| q² h)))`.

This is the "`q`-large" half of the classical quadratic Weyl estimate; the
Gauss weights contribute only their modulus `1`, while the inner sums are
controlled by differencing with the small coefficient `β q²`.
-/

set_option maxHeartbeats 1200000

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- From a bound on the square to a bound on the modulus (real version). -/
lemma real_le_sqrt_of_sq_le {x K : ℝ} (hK : 0 ≤ K) (h : x ^ 2 ≤ K) : x ≤ Real.sqrt K := by
  calc x ≤ |x| := le_abs_self x
    _ = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h

/-- Block estimate for `α = a/q + β` with differencing on the inner `β`-sums. -/
lemma weyl_alpha_block {q M : ℕ} (hq : 0 < q) (a : ℤ) (β : ℝ)
    (hzero : ∀ h ∈ Finset.Icc 1 (M - 1), 2 * (β * (q : ℝ) ^ 2) * (h : ℝ) ≠ 0)
    (hsmall : ∀ h ∈ Finset.Icc 1 (M - 1), |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range (q * M), E (((a : ℝ) / (q : ℝ) + β) * ((n : ℝ) ^ 2))‖ ^ 2
      ≤ (q : ℝ) ^ 2 * ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
  rw [sum_quad_alpha_split hq a β M]
  have hKnonneg : 0 ≤ (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
      min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|) := by
    positivity
  have hTn : ∀ r ∈ Finset.range q,
      ‖∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))‖
        ≤ Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
    intro r _
    have haff : (∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ)) ^ 2))
        = ∑ m ∈ Finset.range M,
            E ((β * (q : ℝ) ^ 2) * (m : ℝ) ^ 2 + (2 * β * (q : ℝ) * (r : ℝ)) * (m : ℝ)
              + β * (r : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro m _
      congr 1
      push_cast
      ring
    have hsq : ‖∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ)) ^ 2)‖ ^ 2
        ≤ (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
            min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|) := by
      rw [haff]
      exact weyl_affine_bound (β * (q : ℝ) ^ 2) (2 * β * (q : ℝ) * (r : ℝ))
        (β * (r : ℝ) ^ 2) M hzero hsmall
    exact real_le_sqrt_of_sq_le hKnonneg hsq
  have htri : ‖∑ r ∈ Finset.range q,
        E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
          * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))‖
      ≤ (q : ℝ) * Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hstep : (∑ r ∈ Finset.range q,
          ‖E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
            * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))‖)
        ≤ ∑ _r ∈ Finset.range q, Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
            min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, norm_E, one_mul]
      exact hTn r hr
    refine le_trans hstep ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hKnonneg' : 0 ≤ (q : ℝ) * Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
      min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
    positivity
  have hsq2 : ‖∑ r ∈ Finset.range q,
        E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
          * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))‖ ^ 2
      ≤ ((q : ℝ) * Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|))) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [norm_nonneg (∑ r ∈ Finset.range q,
        E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
          * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))), htri]
    · exact htri
  calc ‖∑ r ∈ Finset.range q,
        E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
          * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2))‖ ^ 2
      ≤ ((q : ℝ) * Real.sqrt ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|))) ^ 2 := hsq2
    _ = (q : ℝ) ^ 2 * ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (M - 1),
          min ((M - h : ℕ) : ℝ) (1 / |2 * (β * (q : ℝ) ^ 2) * (h : ℝ)|)) := by
      rw [mul_pow, Real.sq_sqrt hKnonneg]

end

end PEqualNP.Weyl
