import PEqualNP.Weyl.Differ
import PEqualNP.Weyl.Linear

/-!
# Layer 5: bilinear (Type-II) sums

Every `frontier-type2-*` cell needs the same two elementary moves:

* Cauchy–Schwarz in the outer variable `m`
  (`norm_sum_mul_sq_le`),
* the exact expansion of the inner second moment into a double sum
  (`inner_sum_sq`), whose off-diagonal part is controlled by the
  geometric saving `‖∑_{m<M} E (mβ)‖ ≤ min M (1/|β|)` from layer 1c.

This file only records those moves; the resulting Type-II bound is assembled
in `BilinearBound`.
-/

namespace PEqualNP.Weyl

noncomputable section

open Finset

/-! ### A. Cauchy–Schwarz in the outer variable -/

lemma norm_sum_mul_sq_le (M : ℕ) (a z : ℕ → ℂ) :
    ‖∑ m ∈ Finset.range M, a m * z m‖ ^ 2
      ≤ (∑ m ∈ Finset.range M, ‖a m‖ ^ 2) * ∑ m ∈ Finset.range M, ‖z m‖ ^ 2 := by
  have h1 : ‖∑ m ∈ Finset.range M, a m * z m‖
      ≤ ∑ m ∈ Finset.range M, ‖a m‖ * ‖z m‖ := by
    calc ‖∑ m ∈ Finset.range M, a m * z m‖
        ≤ ∑ m ∈ Finset.range M, ‖a m * z m‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.range M, ‖a m‖ * ‖z m‖ := by
          exact Finset.sum_congr rfl (fun m _ => norm_mul _ _)
  have h2 : (0 : ℝ) ≤ ∑ m ∈ Finset.range M, ‖a m‖ * ‖z m‖ :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc ‖∑ m ∈ Finset.range M, a m * z m‖ ^ 2
      ≤ (∑ m ∈ Finset.range M, ‖a m‖ * ‖z m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ m ∈ Finset.range M, ‖a m‖ ^ 2) * ∑ m ∈ Finset.range M, ‖z m‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-! ### B. Product of characters with a conjugated second factor -/

lemma mul_star_E (c d : ℂ) (x y : ℝ) :
    (c * E x) * star (d * E y) = c * star d * E (x - y) := by
  rw [star_mul]
  rw [show c * E x * (star (E y) * star d) = c * (E x * star (E y)) * star d from by ring]
  rw [show c * (E x * star (E y)) * star d = c * star d * E (x - y) from by
    rw [E_mul_conj]; ring]

/-- Exact expansion of the inner second moment. -/
lemma inner_sum_sq (N : ℕ) (b : ℕ → ℂ) (θ : ℝ) :
    ‖∑ n ∈ Finset.range N, b n * E (θ * (n : ℝ))‖ ^ 2
      = ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
          (b n1 * star (b n2) * E (θ * ((n1 : ℝ) - (n2 : ℝ)))).re := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [normSq_sum_range N (z := fun n => b n * E (θ * (n : ℝ)))]
  refine Finset.sum_congr rfl (fun n1 _ => Finset.sum_congr rfl (fun n2 _ => ?_))
  rw [mul_star_E]
  congr 1
  ring

end

end PEqualNP.Weyl
