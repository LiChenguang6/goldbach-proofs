import Mathlib

open scoped BigOperators

/- Research scratch only. The analytic estimate is an explicit hypothesis,
not a new axiom and not a solution of the frozen Goldbach task.
Source: Bennett, Martin, O'Bryant, Rechnitzer, Theorem 1.1 (1.9)-(1.11). -/

namespace BmorScratch

theorem inclusive_sum (q a n : ℕ) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) =
    ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k := by
  classical
  symm
  apply Finset.sum_subset
  · intro k hk
    obtain ⟨hk, hmod⟩ := Finset.mem_filter.mp hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hmod⟩
  · intro k hk hnot
    obtain ⟨hk, hmod⟩ := Finset.mem_filter.mp hk
    have hhi := Finset.mem_range.mp hk
    have hzero : k = 0 := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hmod⟩)
    subst k
    simp

theorem specialize_bmor
    (hBMOR : ∀ (q a : ℕ), 3 ≤ q → q ≤ 10000 → Nat.Coprime a q →
      ∃ c x₀ : ℝ, c ≤ 1/840 ∧ x₀ ≤ 8000000000 ∧
        ∀ n : ℕ, x₀ ≤ (n : ℝ) →
          |(∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = a % q),
            ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
            < c * ((n:ℝ)/Real.log (n:ℝ))) :
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
        ≤ (n:ℝ)/(840 * Real.log (n:ℝ)) := by
  intro q a n hq hq' _ha hcop hn
  obtain ⟨c, x₀, hc, hx₀, h⟩ := hBMOR q a hq (by omega) hcop
  have hn' : (8000000000 : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  rw [inclusive_sum]
  calc
    _ ≤ c * ((n:ℝ)/Real.log (n:ℝ)) := (h n (hx₀.trans hn')).le
    _ ≤ (1/840:ℝ) * ((n:ℝ)/Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_right hc (div_nonneg hnpos hlog.le)
    _ = _ := by field_simp

end BmorScratch
