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

noncomputable def centeredTwist {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
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
  · simp only [characterError, centeredTwist, hχ, ite_false, sub_zero, norm_mul, hi]
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
    simp
  rw [hnorm]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)
    _ = B := by field_simp


/-- The averaged error budget suffices; a uniform bound per character is unnecessary. -/
theorem average_twist_budget {q : ℕ} [NeZero q] (a n : ℕ)
    (ha : Nat.Coprime a q) (B : ℝ)
    (hB : (∑ χ : DirichletCharacter ℂ q, ‖centeredTwist χ n‖) ≤
      (q.totient : ℝ) * B) :
    |psiAP q a n - (n : ℝ) / (q.totient : ℝ)| ≤ B := by
  classical
  apply character_budget_transfer a n ha B
  have hpos : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hsum : (∑ χ : DirichletCharacter ℂ q, ‖characterError a n χ‖) =
      ∑ χ : DirichletCharacter ℂ q, ‖centeredTwist χ n‖ := by
    apply Finset.sum_congr rfl
    intro χ hχ
    exact character_error_norm_eq a n ha χ
  rw [hsum]
  have hnorm : ‖(q.totient : ℂ)⁻¹‖ = (q.totient : ℝ)⁻¹ := by simp
  rw [hnorm]
  calc
    _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hpos.le)
    _ = B := by field_simp

/-- Exact conditional reduction of the frozen target to the averaged analytic budget. -/
theorem bmor_of_average
    (H : ∀ (q n : ℕ) [NeZero q], 3 ≤ q → q ≤ 105 →
      8000000000 ≤ n →
      (∑ χ : DirichletCharacter ℂ q, ‖centeredTwist χ n‖) ≤
        (q.totient : ℝ) * ((n : ℝ) / (840 * Real.log (n : ℝ)))) :
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
        ≤ (n:ℝ)/(840 * Real.log (n:ℝ)) := by
  intro q a n hq hq' _ha hcop hn
  letI : NeZero q := ⟨by omega⟩
  exact average_twist_budget a n hcop _ (H q n hq hq' hn)


/- BMOR, Definition 2.8, p. 441:
   exact antiderivative of the zero-counting upper envelope divided by t².
   This calculus identity has no analytic number theory hypotheses. -/
noncomputable def zeroCountPrimitive (d t : ℝ) : ℝ :=
  (Real.log (d*t/(2*Real.pi*Real.exp 1)))^2/(2*Real.pi) -
    ((399/1000 : ℝ)*Real.log (Real.exp 1*d*t) + (5338/1000 : ℝ))/t

theorem zeroCountPrimitive_hasDerivAt (d t : ℝ) (hd : 0 < d) (ht : 0 < t) :
    HasDerivAt (zeroCountPrimitive d)
      ((t/Real.pi * Real.log (d*t/(2*Real.pi*Real.exp 1)) +
        (399/1000 : ℝ)*Real.log (d*t) + (5338/1000 : ℝ))/t^2) t := by
  have hp : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hA : HasDerivAt (fun x : ℝ => d*x/(2*Real.pi*Real.exp 1))
      (d/(2*Real.pi*Real.exp 1)) t := by
    simpa using ((hasDerivAt_id t).const_mul d).div_const (2*Real.pi*Real.exp 1)
  have hB : HasDerivAt (fun x : ℝ => Real.exp 1*d*x)
      (Real.exp 1*d) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.exp 1*d)
  have hLA := hA.log (by positivity)
  have hLB := hB.log (by positivity)
  have hh := ((hLA.pow 2).div_const (2*Real.pi)).sub
    (((hLB.const_mul (399/1000 : ℝ)).add_const (5338/1000 : ℝ)).div
      (hasDerivAt_id t) ht.ne')
  unfold zeroCountPrimitive
  convert hh using 1
  · funext x
    rfl
  · simp only [id_eq, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 by decide, pow_one]
    rw [show Real.exp 1*d*t = Real.exp 1*(d*t) by ring,
      Real.log_mul he.ne' (mul_pos hd ht).ne', Real.log_exp]
    field_simp [hd.ne', ht.ne', hp.ne', he.ne']
    <;> ring


/- BMOR Proposition 2.5 upper envelope and the integral comparison
   used in the proof of Lemma 2.11, equation (2.11). -/
noncomputable def zeroCountUpper (d t : ℝ) : ℝ :=
  t/Real.pi * Real.log (d*t/(2*Real.pi*Real.exp 1)) +
    (399/1000 : ℝ)*Real.log (d*t) + (5338/1000 : ℝ)

theorem zeroCount_integral_upper (d a b : ℝ) (hd : 0 < d)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, zeroCountUpper d t / t^2) =
      zeroCountPrimitive d b - zeroCountPrimitive d a := by
  have hc : ContinuousOn (fun t : ℝ => zeroCountUpper d t / t^2)
      (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hpos : 0 < t := ha.trans_le ht.1
    apply ContinuousAt.continuousWithinAt
    unfold zeroCountUpper
    fun_prop (disch := positivity)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hc.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact zeroCountPrimitive_hasDerivAt d t hd (ha.trans_le ht.1)

theorem zeroCount_weighted_budget (d a b : ℝ) (hd : 0 < d)
    (ha : 0 < a) (hab : a ≤ b) (N : ℝ → ℝ)
    (hN : ∀ t ∈ Set.Icc a b, N t ≤ zeroCountUpper d t)
    (hint : IntervalIntegrable (fun t => N t / t^2) MeasureTheory.volume a b) :
    (∫ t in a..b, N t / t^2) ≤
      zeroCountPrimitive d b - zeroCountPrimitive d a := by
  have hc : ContinuousOn (fun t : ℝ => zeroCountUpper d t / t^2)
      (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hpos : 0 < t := ha.trans_le ht.1
    apply ContinuousAt.continuousWithinAt
    unfold zeroCountUpper
    fun_prop (disch := positivity)
  rw [← zeroCount_integral_upper d a b hd ha hab]
  apply intervalIntegral.integral_mono_on hab hint hc.intervalIntegrable
  intro t ht
  exact div_le_div_of_nonneg_right (hN t ht) (sq_nonneg t)

theorem zeroCount_endpoint_identity (d H : ℝ) (hd : 0 < d) (hH : 0 < H) :
    zeroCountUpper d H / H + zeroCountPrimitive d H =
      (Real.log (d*H/(2*Real.pi)))^2/(2*Real.pi) -
        1/(2*Real.pi) - (399/1000 : ℝ)/H := by
  have hp := Real.pi_pos
  have he := Real.exp_pos (1:ℝ)
  have hX : 0 < d*H/(2*Real.pi) := by positivity
  unfold zeroCountUpper zeroCountPrimitive
  rw [show d*H/(2*Real.pi*Real.exp 1) =
      (d*H/(2*Real.pi))/(Real.exp 1) by ring,
    Real.log_div hX.ne' he.ne', Real.log_exp,
    show Real.exp 1*d*H = Real.exp 1*(d*H) by ring,
    Real.log_mul he.ne' (mul_pos hd hH).ne', Real.log_exp]
  field_simp
  <;> ring


/- Discrete-to-continuous bridge for BMOR (2.11).
   A finite indexing type permits repeated heights (zero multiplicities).
   Strict counts under the integral avoid ambiguity at jump points. -/
theorem inverseSquare_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1/t^2) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have hp : 0 < t := ha.trans_le ht.1
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := positivity)

theorem inverseSquare_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1/t^2) = 1/a - 1/b := by
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => (not_le_of_gt ha) h.1
  have h := intervalIntegral.integral_zpow (a := a) (b := b) (n := -2)
    (Or.inr ⟨by decide, hzero⟩)
  simpa [zpow_neg, one_div, neg_sub] using h

theorem inverseSquare_step_integral (a b h : ℝ) (ha : 0 < a)
    (hah : a ≤ h) (hhb : h ≤ b) :
    (∫ t in a..b, (1/t^2) - (Set.Iic h).indicator (fun t => 1/t^2) t) =
      1/h - 1/b := by
  have hab := hah.trans hhb
  have hbase := inverseSquare_integrable a b ha hab
  have hind : IntervalIntegrable ((Set.Iic h).indicator (fun t : ℝ => 1/t^2))
      MeasureTheory.volume a b := by
    apply intervalIntegrable_iff.mpr
    exact hbase.def'.integrable.indicator measurableSet_Iic
  rw [intervalIntegral.integral_sub hbase hind]
  rw [intervalIntegral.integral_indicator (f := fun t : ℝ => 1/t^2) ⟨hah, hhb⟩]
  rw [inverseSquare_integral a b ha hab, inverseSquare_integral a h ha hah]
  ring

theorem finite_band_partial_summation {ι : Type*} (s : Finset ι) (h : ι → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hh : ∀ i ∈ s, a ≤ h i ∧ h i ≤ b) :
    (∑ i ∈ s, 1/h i) =
      (s.card : ℝ)/b +
        ∫ t in a..b, ∑ i ∈ s, ((1/t^2) -
          (Set.Iic (h i)).indicator (fun t : ℝ => 1/t^2) t) := by
  classical
  have hbase := inverseSquare_integrable a b ha hab
  have hint (i : ι) (_hi : i ∈ s) :
      IntervalIntegrable (fun t : ℝ => 1/t^2 -
        (Set.Iic (h i)).indicator (fun t : ℝ => 1/t^2) t)
        MeasureTheory.volume a b := by
    apply hbase.sub
    apply intervalIntegrable_iff.mpr
    exact hbase.def'.integrable.indicator measurableSet_Iic
  rw [intervalIntegral.integral_finsetSum hint]
  have heq : (∑ i ∈ s, ∫ t in a..b, 1/t^2 -
        (Set.Iic (h i)).indicator (fun t : ℝ => 1/t^2) t) =
      ∑ i ∈ s, (1/h i - 1/b) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact inverseSquare_step_integral a b (h i) ha (hh i hi).1 (hh i hi).2
  rw [heq, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
  ring

/-- Equation (2.11), once partial summation and the zero-count upper bound
    are instantiated for the actual multiset of Dirichlet L-function zeros.
    The zero-count estimate is still an analytic hypothesis. -/
theorem zeroCount_partialSummation_bound (d a b : ℝ) (hd : 0 < d)
    (ha : 0 < a) (hab : a ≤ b) (N : ℝ → ℝ) (S : ℝ)
    (hN : ∀ t ∈ Set.Icc a b, N t ≤ zeroCountUpper d t)
    (hint : IntervalIntegrable (fun t => N t/t^2) MeasureTheory.volume a b)
    (hPS : S = N b/b - N a/a + ∫ t in a..b, N t/t^2) :
    S ≤ -N a/a - zeroCountPrimitive d a +
      (Real.log (d*b/(2*Real.pi)))^2/(2*Real.pi) -
      1/(2*Real.pi) - (399/1000 : ℝ)/b := by
  have hb : 0 < b := ha.trans_le hab
  have h1 := div_le_div_of_nonneg_right (hN b ⟨hab, le_rfl⟩) hb.le
  have h2 := zeroCount_weighted_budget d a b hd ha hab N hN hint
  have h3 := zeroCount_endpoint_identity d b hd hb
  rw [hPS]
  linarith

end BmorScratch
