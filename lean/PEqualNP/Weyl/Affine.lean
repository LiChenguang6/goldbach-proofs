import PEqualNP.Weyl.Weyl

/-!
# Layer 4b: Weyl differencing for affine-quadratic phases

The residue decomposition of `Weyl/Alpha.lean` produces inner sums whose
summand is `E (β (q m + r)²)`, i.e. an *affine* quadratic phase
`c m² + d m + e` with `c = β q²`, `d = 2 β q r`, `e = β r²`.
The same differencing argument as for `E (α n²)` applies once the shift
identity is generalised to this affine shape.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- Difference phase for an affine-quadratic character:
the ratio of the `(n+h)`-term and the `n`-term is the phase of the increment. -/
lemma E_affine_shift (c d e : ℝ) (n h : ℕ) :
    E (c * (((n + h : ℕ) : ℝ)) ^ 2 + d * (((n + h : ℕ) : ℝ)) + e)
        * star (E (c * ((n : ℝ)) ^ 2 + d * ((n : ℝ)) + e))
      = E (2 * c * (h : ℝ) * (n : ℝ) + c * (h : ℝ) ^ 2 + d * (h : ℝ)) := by
  rw [E_mul_conj]
  congr 1
  push_cast
  ring

/-- Weyl differencing for the affine-quadratic phase `c n² + d n + e`. -/
lemma weyl_affine (c d e : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, E (c * (n : ℝ) ^ 2 + d * (n : ℝ) + e)‖ ^ 2
      ≤ (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
          ‖∑ k ∈ Finset.range (N - h),
            E (2 * c * (h : ℝ) * (k : ℝ) + c * (h : ℝ) ^ 2 + d * (h : ℝ))‖ := by
  have hmain := differ_bound N (fun n => E (c * (n : ℝ) ^ 2 + d * (n : ℝ) + e))
  have hdiag : (∑ n ∈ Finset.range N, ‖E (c * (n : ℝ) ^ 2 + d * (n : ℝ) + e)‖ ^ 2)
      = (N : ℝ) := by
    have h1 : ∀ n ∈ Finset.range N,
        ‖E (c * (n : ℝ) ^ 2 + d * (n : ℝ) + e)‖ ^ 2 = (1 : ℝ) := by
      intro n _
      rw [norm_E]
      norm_num
    rw [Finset.sum_congr rfl h1]
    simp
  rw [hdiag] at hmain
  have hinner : (∑ h ∈ Finset.Icc 1 (N - 1),
        ‖∑ k ∈ Finset.range (N - h),
          E (c * (((k + h : ℕ) : ℝ)) ^ 2 + d * (((k + h : ℕ) : ℝ)) + e)
            * star (E (c * ((k : ℝ)) ^ 2 + d * ((k : ℝ)) + e))‖)
      = ∑ h ∈ Finset.Icc 1 (N - 1),
          ‖∑ k ∈ Finset.range (N - h),
            E (2 * c * (h : ℝ) * (k : ℝ) + c * (h : ℝ) ^ 2 + d * (h : ℝ))‖ := by
    apply Finset.sum_congr rfl
    intro h _
    exact congrArg (fun z : ℂ => ‖z‖)
      (Finset.sum_congr rfl (fun k _ => E_affine_shift c d e k h))
  rw [hinner] at hmain
  exact hmain

/-- The inner linear sums of the affine differencing are bounded by the `min` form. -/
lemma weyl_affine_inner (c d : ℝ) (N h : ℕ)
    (h0 : 2 * c * (h : ℝ) ≠ 0) (h1 : |2 * c * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ k ∈ Finset.range (N - h),
        E (2 * c * (h : ℝ) * (k : ℝ) + c * (h : ℝ) ^ 2 + d * (h : ℝ))‖
      ≤ min ((N - h : ℕ) : ℝ) (1 / |2 * c * (h : ℝ)|) := by
  have hrew : (∑ k ∈ Finset.range (N - h),
        E (2 * c * (h : ℝ) * (k : ℝ) + c * (h : ℝ) ^ 2 + d * (h : ℝ)))
      = ∑ k ∈ Finset.range (N - h),
          E ((k : ℝ) * (2 * c * (h : ℝ)) + (c * (h : ℝ) ^ 2 + d * (h : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast
    ring
  rw [hrew, norm_sum_E_add_const (c := 2 * c * (h : ℝ))
    (d := c * (h : ℝ) ^ 2 + d * (h : ℝ))]
  exact norm_sum_E_le_min h0 h1 (N - h)

/-- Assembled affine Weyl bound with the `min`-form inner estimates. -/
lemma weyl_affine_bound (c d e : ℝ) (N : ℕ)
    (hzero : ∀ h ∈ Finset.Icc 1 (N - 1), 2 * c * (h : ℝ) ≠ 0)
    (hsmall : ∀ h ∈ Finset.Icc 1 (N - 1), |2 * c * (h : ℝ)| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range N, E (c * (n : ℝ) ^ 2 + d * (n : ℝ) + e)‖ ^ 2
      ≤ (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
          min ((N - h : ℕ) : ℝ) (1 / |2 * c * (h : ℝ)|) := by
  refine le_trans (weyl_affine c d e N) ?_
  gcongr
  exact weyl_affine_inner c d N _ (hzero _ ‹_›) (hsmall _ ‹_›)

end

end PEqualNP.Weyl
