import Mathlib

open scoped BigOperators

namespace BmorScratch

noncomputable def psiAP (q a n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k

noncomputable def psiTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)

/- Exact finite character expansion, not an asymptotic estimate.
   Uses Mathlib's residueClass_apply at the pinned revision. -/
theorem psiAP_character_expansion {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) :
    (psiAP q a n : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiTwist χ n := by
  classical
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        (ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) k : ℂ) := by
      unfold psiAP
      rw [Finset.sum_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro k hk
      simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
        Set.mem_setOf_eq, ZMod.natCast_eq_natCast_iff']
      split_ifs <;> simp_all
    _ = ∑ k ∈ Finset.range (n+1),
        ((q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) * χ (k : ZMod q) *
              (ArithmeticFunction.vonMangoldt k : ℂ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact ArithmeticFunction.vonMangoldt.residueClass_apply hu k
    _ = _ := by
      simp only [psiTwist, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
      rw [← Finset.mul_sum, Finset.sum_comm]
      apply congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z)
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/- Center the character sum by subtracting the trivial-character main term. -/
noncomputable def characterError {q : ℕ} [NeZero q] (a n : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  χ ((a : ZMod q)⁻¹) * psiTwist χ n - if χ = 1 then (n : ℂ) else 0

theorem centered_character_expansion {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) :
    (psiAP q a n : ℂ) - (n : ℂ) / (q.totient : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, characterError a n χ := by
  classical
  rw [psiAP_character_expansion a n ha]
  simp only [characterError, Finset.sum_sub_distrib]
  have h : (∑ χ : DirichletCharacter ℂ q,
      if χ = 1 then (n : ℂ) else 0) = n := by simp
  rw [h]
  ring

/- The remaining analytic obligation is a bound on the sum of these errors.
   This lemma does not assert such a bound without a hypothesis. -/
theorem character_budget_transfer {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) (B : ℝ)
    (hB : ‖(q.totient : ℂ)⁻¹‖ *
      (∑ χ : DirichletCharacter ℂ q, ‖characterError a n χ‖) ≤ B) :
    |psiAP q a n - (n : ℝ) / (q.totient : ℝ)| ≤ B := by
  have hcast : ‖(psiAP q a n : ℂ) - (n : ℂ) / (q.totient : ℂ)‖ =
      |psiAP q a n - (n : ℝ) / (q.totient : ℝ)| := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_natCast q.totient,
      ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [← hcast, centered_character_expansion a n ha, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans hB

end BmorScratch
