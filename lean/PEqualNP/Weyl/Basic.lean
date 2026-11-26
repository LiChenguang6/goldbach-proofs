import Mathlib

/-!
# Weyl / Vinogradov infrastructure, layer 0

Basic objects shared by every later estimate: the additive character `E`,
the polynomial `S n u t`, and the elementary norm bounds that any
minor-arc argument starts from.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- The additive character `e(x) = exp(2πix)`, as in the desk statements. -/
def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Exponential polynomial with real coefficients `u`. -/
def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((u k : ℝ) : ℂ) * E ((k : ℝ) * t)

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  rw [Complex.norm_exp]
  have h : (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  rw [h]
  simp

lemma norm_coeff_mul_E (u : ℝ) (x : ℝ) : ‖(u : ℂ) * E x‖ = |u| := by
  rw [norm_mul, norm_E, Complex.norm_real, Real.norm_eq_abs, mul_one]

/-- Trivial sup bound: `‖S n u t‖ ≤ ∑ |u k|`, uniform in `t`. -/
lemma norm_S_le (n : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    ‖S n u t‖ ≤ ∑ k ∈ Finset.range (n + 1), |u k| := by
  unfold S
  calc ‖∑ k ∈ Finset.range (n + 1), ((u k : ℝ) : ℂ) * E ((k : ℝ) * t)‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖((u k : ℝ) : ℂ) * E ((k : ℝ) * t)‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), |u k| := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        exact norm_coeff_mul_E (u k) ((k : ℝ) * t)

/-- The character is multiplicative in the argument. -/
lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `E` has period one. -/
lemma E_period (x : ℝ) : E (x + 1) = E x := by
  rw [E_add]
  have h : E (1 : ℝ) = 1 := by
    unfold E
    rw [show (((2 * Real.pi * (1 : ℝ) : ℝ) : ℂ) * Complex.I) =
        (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_two_pi_mul_I]
  rw [h, mul_one]

/-- `E (k α) = (E α)^k`. -/
lemma E_nat_mul (k : ℕ) (α : ℝ) : E ((k : ℝ) * α) = (E α) ^ k := by
  induction k with
  | zero => simp [E]
  | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, E_add, ih, pow_succ]

/-- Layer 1: geometric (linear) Weyl bound.  For `E α ≠ 1` and `N ≥ 1`,
`‖∑_{k<N} E (k α)‖ ≤ 2 / ‖E α - 1‖`. -/
lemma norm_geom_le (α : ℝ) (N : ℕ) (h : E α ≠ 1) :
    ‖∑ k ∈ Finset.range N, E ((k : ℝ) * α)‖ ≤ 2 / ‖E α - 1‖ := by
  have hsum : ∑ k ∈ Finset.range N, E ((k : ℝ) * α) = ((E α) ^ N - 1) / (E α - 1) := by
    rw [show (∑ k ∈ Finset.range N, E ((k : ℝ) * α))
          = ∑ k ∈ Finset.range N, (E α) ^ k from by
        exact Finset.sum_congr rfl (fun k _ => E_nat_mul k α)]
    exact geom_sum_eq h N
  rw [hsum, norm_div]
  have hx : ‖E α‖ = 1 := norm_E α
  have hnum : ‖(E α) ^ N - 1‖ ≤ 2 := by
    calc ‖(E α) ^ N - 1‖ ≤ ‖(E α) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hx]; norm_num
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

end

end PEqualNP.Weyl
