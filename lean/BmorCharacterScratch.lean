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
        Set.mem_ofPred_eq, ZMod.natCast_eq_natCast_iff']
    _ = ∑ k ∈ Finset.range (n+1),
        ((q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) * χ (k : ZMod q) *
              (ArithmeticFunction.vonMangoldt k : ℂ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact ArithmeticFunction.vonMangoldt.residueClass_apply hu k
    _ = _ := by
      simp only [psiTwist, ← Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      apply congrArg (fun z : ℂ => (q.totient : ℂ)⁻¹ * z)
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [Finset.mul_sum]

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


/- The principal character removes precisely the integers not coprime to q. -/
theorem principal_twist_eq {q : ℕ} [NeZero q] (n : ℕ) :
    psiTwist (1 : DirichletCharacter ℂ q) n =
      (∑ k ∈ Finset.range (n+1), ArithmeticFunction.vonMangoldt k : ℝ) -
      (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k : ℝ) := by
  classical
  unfold psiTwist
  rw [Finset.sum_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : Nat.Coprime k q
  · have hu := (ZMod.isUnit_iff_coprime k q).2 h
    simp [h, MulChar.one_apply hu]
  · have hu : ¬ IsUnit (k : ZMod q) := fun h' =>
      h ((ZMod.isUnit_iff_coprime k q).1 h')
    simp [h, MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hu]

noncomputable def centeredTwist {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  psiTwist χ n - if χ = 1 then (n : ℂ) else 0

/-- The absolute character error is independent of the reduced residue a. -/
theorem character_error_norm_eq {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) (χ : DirichletCharacter ℂ q) :
    ‖characterError a n χ‖ = ‖centeredTwist χ n‖ := by
  classical
  let u := ZMod.unitOfCoprime a ha
  have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a ha
  have hi : ((a : ZMod q)⁻¹) = (u⁻¹ : (ZMod q)ˣ) := by
    rw [← hu, ZMod.inv_coe_unit]
  by_cases hχ : χ = 1
  · subst χ
    simp [characterError, centeredTwist, hi, MulChar.one_apply_coe]
  · simp only [characterError, centeredTwist, hχ, if_false, sub_zero, norm_mul, hi]
    rw [χ.unit_norm_eq_one (u⁻¹), one_mul]

/-- A uniform bound for the centered twists suffices for the AP error bound.
    The analytic bound remains a hypothesis, not a proved estimate. -/
theorem uniform_twist_budget {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) (B : ℝ)
    (hB : ∀ χ : DirichletCharacter ℂ q, ‖centeredTwist χ n‖ ≤ B) :
    |psiAP q a n - (n : ℝ) / (q.totient : ℝ)| ≤ B := by
  classical
  apply character_budget_transfer a n ha B
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hpos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hs : (∑ χ : DirichletCharacter ℂ q, ‖characterError a n χ‖) ≤
      (q.totient : ℝ) * B := by
    calc
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, B := by
        apply Finset.sum_le_sum
        intro χ hχ
        rw [character_error_norm_eq a n ha χ]
        exact hB χ
      _ = _ := by simp [hcard, nsmul_eq_mul]
  have hnorm : ‖(q.totient : ℂ)⁻¹‖ = (q.totient : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_natCast, Real.norm_eq_abs]
  rw [hnorm]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)
    _ = B := by field_simp

end BmorScratch
