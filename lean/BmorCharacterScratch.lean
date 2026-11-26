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
  have h := integral_zpow (a := a) (b := b) (n := -2)
    (Or.inr ⟨by decide, hzero⟩)
  norm_num [zpow_neg, one_div, neg_sub] at h ⊢
  linarith only [h]

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
  have heq : (∫ t in a..b, (Set.Iic h).indicator (fun t : ℝ => 1/t^2) t) =
      ∫ t in a..h, 1/t^2 := by
    exact intervalIntegral.integral_indicator (μ := MeasureTheory.volume)
      (f := fun t : ℝ => 1/t^2) ⟨hah, hhb⟩
  rw [heq]
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
  rw [hPS, neg_div]
  linarith only [h1, h2, h3]


/- Standard zero term estimates used with a truncated explicit formula.
   No zero-free region, GRH or zero-counting assertion is assumed implicitly. -/
theorem zeroTerm_norm (x : ℝ) (ρ : ℂ) (hx : 0 < x) :
    ‖(x : ℂ)^ρ / ρ‖ = x^ρ.re / ‖ρ‖ := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem zeroTerm_height_bound (x σ : ℝ) (ρ : ℂ)
    (hx : 1 ≤ x) (hre : ρ.re ≤ σ) (hi : 0 < |ρ.im|) :
    ‖(x : ℂ)^ρ / ρ‖ ≤ x^σ / |ρ.im| := by
  rw [zeroTerm_norm x ρ (by linarith)]
  have hnorm : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  calc
    _ ≤ x^σ / ‖ρ‖ := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx hre) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _)
      hi hnorm

theorem zeroBand_norm_bound {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (x σ : ℝ) (hx : 1 ≤ x) (hre : ∀ i ∈ s, (ρ i).re ≤ σ)
    (hi : ∀ i ∈ s, 0 < |(ρ i).im|) :
    ‖∑ i ∈ s, (x : ℂ)^(ρ i) / ρ i‖ ≤
      x^σ * ∑ i ∈ s, 1/|(ρ i).im| := by
  calc
    _ ≤ ∑ i ∈ s, ‖(x : ℂ)^(ρ i) / ρ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, x^σ / |(ρ i).im| := by
      exact Finset.sum_le_sum (fun i hi' =>
        zeroTerm_height_bound x σ (ρ i) hx (hre i hi') (hi i hi'))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      ring

/-- When the critical-line calculation is available, the low zero band
    has the exact square-root scaling in the explicit formula. -/
theorem criticalLine_band_bound {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (x : ℝ) (hx : 1 ≤ x)
    (hre : ∀ i ∈ s, (ρ i).re = 1/2)
    (hi : ∀ i ∈ s, 0 < |(ρ i).im|) :
    ‖∑ i ∈ s, (x : ℂ)^(ρ i) / ρ i‖ ≤
      Real.sqrt x * ∑ i ∈ s, 1/|(ρ i).im| := by
  rw [Real.sqrt_eq_rpow]
  exact zeroBand_norm_bound s ρ x (1/2) hx (fun i h => (hre i h).le) hi

/-- For a real-part gap δ, isolate the exponential decay factor. -/
theorem rpow_zeroFree_decay (x δ : ℝ) (hx : 0 < x) :
    x^(1-δ) = x * Real.exp (-δ * Real.log x) := by
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * (1-δ) = Real.log x + (-δ * Real.log x) by ring,
    Real.exp_add, Real.exp_log hx]

theorem zeroFree_band_bound {ι : Type*} (s : Finset ι) (ρ : ι → ℂ)
    (x δ : ℝ) (hx : 1 ≤ x)
    (hre : ∀ i ∈ s, (ρ i).re ≤ 1-δ)
    (hi : ∀ i ∈ s, 0 < |(ρ i).im|) :
    ‖∑ i ∈ s, (x : ℂ)^(ρ i) / ρ i‖ ≤
      x * Real.exp (-δ * Real.log x) * ∑ i ∈ s, 1/|(ρ i).im| := by
  rw [← rpow_zeroFree_decay x δ (by linarith)]
  exact zeroBand_norm_bound s ρ x (1-δ) hx hre hi

/-- Combine disjoint zero bands and the analytic truncation remainder.
    The explicit-formula equality and zero-free estimates remain hypotheses. -/
theorem explicitFormula_three_bands {ι : Type*} (s₁ s₂ s₃ : Finset ι)
    (ρ : ι → ℂ) (x δ : ℝ) (E R : ℂ) (B : ℝ)
    (hx : 1 ≤ x)
    (h₁ : ∀ i ∈ s₁, (ρ i).re = 1/2)
    (h₂ : ∀ i ∈ s₂, (ρ i).re ≤ 1-δ)
    (h₃ : ∀ i ∈ s₃, (ρ i).re ≤ 1)
    (hi₁ : ∀ i ∈ s₁, 0 < |(ρ i).im|)
    (hi₂ : ∀ i ∈ s₂, 0 < |(ρ i).im|)
    (hi₃ : ∀ i ∈ s₃, 0 < |(ρ i).im|)
    (hR : ‖R‖ ≤ B)
    (hE : E = -(∑ i ∈ s₁, (x : ℂ)^(ρ i)/ρ i) -
      (∑ i ∈ s₂, (x : ℂ)^(ρ i)/ρ i) -
      (∑ i ∈ s₃, (x : ℂ)^(ρ i)/ρ i) + R) :
    ‖E‖ ≤ Real.sqrt x * (∑ i ∈ s₁, 1/|(ρ i).im|) +
      x * Real.exp (-δ * Real.log x) * (∑ i ∈ s₂, 1/|(ρ i).im|) +
      x * (∑ i ∈ s₃, 1/|(ρ i).im|) + B := by
  have ha := criticalLine_band_bound s₁ ρ x hx h₁ hi₁
  have hb := zeroFree_band_bound s₂ ρ x δ hx h₂ hi₂
  have hc := zeroBand_norm_bound s₃ ρ x 1 hx h₃ hi₃
  rw [Real.rpow_one] at hc
  rw [hE]
  calc
    _ ≤ ‖-(∑ i ∈ s₁, (x : ℂ)^(ρ i)/ρ i) -
        (∑ i ∈ s₂, (x : ℂ)^(ρ i)/ρ i) -
        (∑ i ∈ s₃, (x : ℂ)^(ρ i)/ρ i)‖ + ‖R‖ := norm_add_le _ _
    _ ≤ _ := by
      have hd := norm_sub_le (-(∑ i ∈ s₁, (x : ℂ)^(ρ i)/ρ i) -
        (∑ i ∈ s₂, (x : ℂ)^(ρ i)/ρ i))
        (∑ i ∈ s₃, (x : ℂ)^(ρ i)/ρ i)
      have he := norm_sub_le (-(∑ i ∈ s₁, (x : ℂ)^(ρ i)/ρ i))
        (∑ i ∈ s₂, (x : ℂ)^(ρ i)/ρ i)
      rw [norm_neg] at he
      linarith only [ha, hb, hc, hd, he, hR]


/- BMOR primitive-character reduction: a character induced from a smaller
   modulus differs only at the nonunits of the larger modulus. -/
theorem changeLevel_apply_nat {d q : ℕ} (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (DirichletCharacter.changeLevel hd χ) (k : ZMod q) =
      if Nat.Coprime k q then χ (k : ZMod d) else 0 := by
  by_cases hk : Nat.Coprime k q
  · rw [if_pos hk]
    have h := χ.changeLevel_eq_cast_of_dvd hd (ZMod.unitOfCoprime k hk)
    simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd] using h
  · rw [if_neg hk]
    exact MulChar.map_nonunit _ (fun hu => hk ((ZMod.isUnit_iff_coprime k q).1 hu))

theorem changeLevel_twist_difference {d q : ℕ} (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    psiTwist χ n - psiTwist (DirichletCharacter.changeLevel hd χ) n =
      ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        χ (k : ZMod d) * (ArithmeticFunction.vonMangoldt k : ℂ) := by
  classical
  unfold psiTwist
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  rw [changeLevel_apply_nat hd χ k]
  split_ifs <;> simp_all

theorem changeLevel_twist_bound {d q : ℕ} [NeZero d] (hd : d ∣ q)
    (χ : DirichletCharacter ℂ d) (n : ℕ) :
    ‖psiTwist χ n - psiTwist (DirichletCharacter.changeLevel hd χ) n‖ ≤
      ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k := by
  rw [changeLevel_twist_difference hd χ n]
  calc
    _ ≤ ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ‖χ (k : ZMod d) * (ArithmeticFunction.vonMangoldt k : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (χ.norm_le_one (k : ZMod d))

/-- Bound the imprimitive character correction by the nonunit prime-power
    mass.  The cardinal/logarithmic estimate for that mass is a separate
    number-theoretic input, not an axiom introduced in this development. -/
theorem primitive_twist_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖psiTwist χ.primitiveCharacter n - psiTwist χ n‖ ≤
      ∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := changeLevel_twist_bound χ.conductor_dvd_level χ.primitiveCharacter n
  rw [χ.changeLevel_primitiveCharacter] at h
  exact h

theorem primitive_principal_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  · intro h
    subst χ
    exact DirichletCharacter.primitiveCharacter_one

theorem primitive_centered_error_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (B D : ℝ) (hB : ‖psiTwist χ.primitiveCharacter n -
      (if χ = 1 then (n : ℂ) else 0)‖ ≤ B)
    (hD : (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k) ≤ D) :
    ‖centeredTwist χ n‖ ≤ B + D := by
  have hd := primitive_twist_bound χ n
  have hh : centeredTwist χ n =
      (psiTwist χ.primitiveCharacter n - (if χ = 1 then (n : ℂ) else 0)) -
      (psiTwist χ.primitiveCharacter n - psiTwist χ n) := by
    unfold centeredTwist
    ring
  rw [hh]
  exact (norm_sub_le _ _).trans (add_le_add hB (hd.trans hD))


/- Elementary nonunit mass bound.  Adapted from Nature-UL's public proof
   of L-goldbach-finite-fixed-nonunit-mangoldt, upstream PR #2444,
   https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2444
   (Apache-2.0). Included locally in the research file, not imported as
   an undeclared external lemma or represented as a new platform proof. -/
theorem nonunit_mangoldt_bound (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
      ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card:ℝ)*Real.log n := by
  classical
  let M := ∏ p ∈ q.primeFactors, p ^ Nat.log p n
  have hM : 0 < M := Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  let S := (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q)
  have hsupport : S.filter (fun k => ArithmeticFunction.vonMangoldt k ≠ 0) ⊆ M.divisors := by
    intro k hk
    obtain ⟨hkS, hweight⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkrange, hnonunit⟩ := Finset.mem_filter.mp hkS
    obtain ⟨p, j, hp, _, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hweight
    have hprime := Nat.prime_iff.mpr hp
    have hdvd : p ∣ q := by
      by_contra h
      exact hnonunit ((hprime.coprime_iff_not_dvd.mpr h).pow_left j)
    have hpq := Nat.mem_primeFactors.mpr ⟨hprime, hdvd, Nat.ne_of_gt hq⟩
    have hj : j ≤ Nat.log p n :=
      Nat.le_log_of_pow_le hprime.one_lt (Finset.mem_range_succ_iff.mp hkrange)
    exact Nat.mem_divisors.mpr ⟨(pow_dvd_pow p hj).trans
      (Finset.dvd_prod_of_mem (fun r => r ^ Nat.log r n) hpq), hM.ne'⟩
  have hbound : M ≤ n ^ q.primeFactors.card := by
    calc
      M ≤ ∏ _p ∈ q.primeFactors, n :=
        Finset.prod_le_prod fun p _ => Nat.pow_log_le_self p (Nat.ne_of_gt hn)
      _ = _ := Finset.prod_const n
  change (∑ k ∈ S, ArithmeticFunction.vonMangoldt k) ≤ _
  rw [← Finset.sum_filter_ne_zero (f := fun k => ArithmeticFunction.vonMangoldt k) S]
  calc
    _ ≤ ∑ k ∈ M.divisors, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log M := ArithmeticFunction.vonMangoldt_sum
    _ ≤ Real.log ((n ^ q.primeFactors.card : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hbound)
    _ = _ := by rw [Nat.cast_pow, Real.log_pow]

/-- Four distinct prime factors already force a modulus of at least 210.
    This avoids opaque factorization evaluation and native_decide. -/
theorem small_modulus_primeFactor_card (q : ℕ) (hq : q ≤ 105) :
    q.primeFactors.card ≤ 3 := by
  classical
  by_cases hz : q = 0
  · simp [hz]
  by_contra! hc
  let s := q.primeFactors
  change 3 < s.card at hc
  have hs : 0 < s.card := by omega
  let p₁ := s.min' (Finset.card_pos.mp hs)
  have hp₁ : p₁ ∈ s := Finset.min'_mem _ _
  let s₁ := s.erase p₁
  have hc₁ : s₁.card = s.card - 1 := Finset.card_erase_of_mem hp₁
  have hs₁ : 0 < s₁.card := by omega
  let p₂ := s₁.min' (Finset.card_pos.mp hs₁)
  have hp₂ : p₂ ∈ s₁ := Finset.min'_mem _ _
  let s₂ := s₁.erase p₂
  have hc₂ : s₂.card = s₁.card - 1 := Finset.card_erase_of_mem hp₂
  have hs₂ : 0 < s₂.card := by omega
  let p₃ := s₂.min' (Finset.card_pos.mp hs₂)
  have hp₃ : p₃ ∈ s₂ := Finset.min'_mem _ _
  let s₃ := s₂.erase p₃
  have hc₃ : s₃.card = s₂.card - 1 := Finset.card_erase_of_mem hp₃
  have hs₃ : 0 < s₃.card := by omega
  let p₄ := s₃.min' (Finset.card_pos.mp hs₃)
  have hp₄ : p₄ ∈ s₃ := Finset.min'_mem _ _
  let s₄ := s₃.erase p₄
  have hsub₁ : s₁ ⊆ s := Finset.erase_subset _ _
  have hsub₂ : s₂ ⊆ s₁ := Finset.erase_subset _ _
  have hsub₃ : s₃ ⊆ s₂ := Finset.erase_subset _ _
  have hsub₄ : s₄ ⊆ s₃ := Finset.erase_subset _ _
  have hprime (p : ℕ) (hp : p ∈ s) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h12 : p₁ < p₂ :=
    lt_of_le_of_ne (Finset.min'_le s p₂ (hsub₁ hp₂)) (Finset.mem_erase.mp hp₂).1.symm
  have h23 : p₂ < p₃ :=
    lt_of_le_of_ne (Finset.min'_le s₁ p₃ (hsub₂ hp₃)) (Finset.mem_erase.mp hp₃).1.symm
  have h34 : p₃ < p₄ :=
    lt_of_le_of_ne (Finset.min'_le s₂ p₄ (hsub₃ hp₄)) (Finset.mem_erase.mp hp₄).1.symm
  have h1 : 2 ≤ p₁ := (hprime p₁ hp₁).two_le
  have h2 : 3 ≤ p₂ := by omega
  have h3 : 5 ≤ p₃ := by
    by_contra! h
    have heq : p₃ = 4 := by omega
    have hp := hprime p₃ (hsub₁ (hsub₂ hp₃))
    rw [heq] at hp
    exact (by decide : ¬ Nat.Prime 4) hp
  have h4 : 7 ≤ p₄ := by
    by_contra! h
    have heq : p₄ = 6 := by omega
    have hp := hprime p₄ (hsub₁ (hsub₂ (hsub₃ hp₄)))
    rw [heq] at hp
    exact (by decide : ¬ Nat.Prime 6) hp
  have hrest : 1 ≤ ∏ p ∈ s₄, p := by
    exact Finset.prod_pos (fun p hp =>
      (hprime p (hsub₁ (hsub₂ (hsub₃ (hsub₄ hp))))).pos)
  have e₁ : p₁ * (∏ p ∈ s₁, p) = ∏ p ∈ s, p :=
    Finset.mul_prod_erase s id hp₁
  have e₂ : p₂ * (∏ p ∈ s₂, p) = ∏ p ∈ s₁, p :=
    Finset.mul_prod_erase s₁ id hp₂
  have e₃ : p₃ * (∏ p ∈ s₃, p) = ∏ p ∈ s₂, p :=
    Finset.mul_prod_erase s₂ id hp₃
  have e₄ : p₄ * (∏ p ∈ s₄, p) = ∏ p ∈ s₃, p :=
    Finset.mul_prod_erase s₃ id hp₄
  have hmul : 210 ≤ p₁*(p₂*(p₃*(p₄*(∏ p ∈ s₄, p)))) := by
    calc
      210 = 2*(3*(5*(7*1))) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 (Nat.mul_le_mul h4 hrest)))
  rw [e₄, e₃, e₂, e₁] at hmul
  have hprod : (∏ p ∈ s, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) (Nat.prod_primeFactors_dvd q)
  omega

/-- For the frozen threshold, the correction 3 log x takes at most 1%
    of x/(840 log x). The proof uses only elementary real inequalities. -/
theorem nonunit_budget_real (x : ℝ) (hx : 8000000000 ≤ x) :
    3 * Real.log x ≤ x/(84000 * Real.log x) := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  let u : ℝ := x^(1/8:ℝ)
  have hu : 0 < u := Real.rpow_pos_of_pos hxpos _
  have hu8 : u^8 = x := by
    unfold u
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    norm_num
  have hu16 : 16 ≤ u := by
    by_contra! h
    have h8 : u^8 < (16:ℝ)^8 := by gcongr
    norm_num at h8
    linarith
  have hl : Real.log x ≤ 8*u := by
    have h := Real.log_le_rpow_div hxpos.le (by norm_num : (0:ℝ)<1/8)
    change Real.log x ≤ u/(1/8:ℝ) at h
    linarith
  have hl2 : (Real.log x)^2 ≤ (8*u)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ 8*u + Real.log x by positivity)]
  have hu6 : (16:ℝ)^6 ≤ u^6 := by gcongr
  have hb : (252000*64:ℝ) ≤ u^6 := by norm_num at hu6 ⊢; linarith
  have hp := mul_le_mul_of_nonneg_right hb (sq_nonneg u)
  have ht : (252000:ℝ)*(Real.log x)^2 ≤ x := by
    calc
      _ ≤ 252000*(8*u)^2 := mul_le_mul_of_nonneg_left hl2 (by norm_num)
      _ = (252000*64:ℝ)*u^2 := by ring
      _ ≤ u^6*u^2 := hp
      _ = x := by rw [← pow_add, hu8]
  apply (le_div_iff₀ (by positivity : 0 < 84000 * Real.log x)).2
  nlinarith only [ht]

theorem nonunit_small_modulus_budget (q n : ℕ) (hq : 1 ≤ q)
    (hq' : q ≤ 105) (hn : 8000000000 ≤ n) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
      ArithmeticFunction.vonMangoldt k) ≤ (n:ℝ)/(84000 * Real.log n) := by
  have hc : (q.primeFactors.card:ℝ) ≤ 3 := by
    exact_mod_cast small_modulus_primeFactor_card q hq'
  have hn' : (8000000000:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith)
  exact (nonunit_mangoldt_bound q n hq (by omega)).trans
    ((mul_le_mul_of_nonneg_right hc hlog).trans (nonunit_budget_real n hn'))

/-- Reduce the frozen estimate to the primitive-character analytic budget
    with a separately proved explicit allowance for changing modulus. -/
theorem bmor_of_primitive_budget
    (H : ∀ (q n : ℕ) [NeZero q], 3 ≤ q → q ≤ 105 → 8000000000 ≤ n →
      (∑ χ : DirichletCharacter ℂ q, ‖psiTwist χ.primitiveCharacter n -
        (if χ = 1 then (n : ℂ) else 0)‖) ≤
          (q.totient : ℝ) * (99/100 * ((n:ℝ)/(840 * Real.log n)))) :
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      8000000000 ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q|
        ≤ (n:ℝ)/(840 * Real.log (n:ℝ)) := by
  classical
  apply bmor_of_average
  intro q n _ hq hq' hn
  let D : ℝ := (n:ℝ)/(84000*Real.log n)
  let B : ℝ := (n:ℝ)/(840*Real.log n)
  have hD := nonunit_small_modulus_budget q n (by omega) hq' hn
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hD' : D = B/100 := by
    dsimp [D, B]
    have hlog : Real.log (n:ℝ) ≠ 0 := (Real.log_pos
      (by have hn' : (8000000000:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
          linarith)).ne'
    field_simp [hlog]
    <;> ring
  have hH := H q n hq hq' hn
  change (∑ χ : DirichletCharacter ℂ q, ‖centeredTwist χ n‖) ≤ (q.totient:ℝ)*B
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, (‖psiTwist χ.primitiveCharacter n -
        (if χ = 1 then (n:ℂ) else 0)‖ + D) := by
      apply Finset.sum_le_sum
      intro χ hχ
      exact primitive_centered_error_bound χ n _ D le_rfl hD
    _ = (∑ χ : DirichletCharacter ℂ q, ‖psiTwist χ.primitiveCharacter n -
          (if χ = 1 then (n:ℂ) else 0)‖) + (q.totient:ℝ)*D := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    _ ≤ (q.totient:ℝ)*(99/100*B) + (q.totient:ℝ)*D :=
      add_le_add hH le_rfl
    _ = _ := by rw [hD']; ring


/- BMOR Lemma 2.18, integration of the logarithmic zero-count envelope.
   A finite-interval estimate is sufficient for any truncated zero sum;
   it is uniform in the upper endpoint. -/
noncomputable def logPowerTailPrimitive (d m t : ℝ) : ℝ :=
  -(Real.log (d*t)/m + 1/m^2) * Real.exp (-m*Real.log t)

theorem logPowerTailPrimitive_hasDerivAt (d m t : ℝ) (hd : 0 < d)
    (hm : 0 < m) (ht : 0 < t) :
    HasDerivAt (logPowerTailPrimitive d m)
      (Real.log (d*t)*Real.exp (-m*Real.log t)/t) t := by
  have hdt : HasDerivAt (fun z : ℝ => d*z) d t := by
    simpa using (hasDerivAt_id t).const_mul d
  have hL := (hdt.log (mul_ne_zero hd.ne' ht.ne')).div_const m
  have hR := ((Real.hasDerivAt_log ht.ne').const_mul (-m)).exp
  have h := (hL.add_const (1/m^2)).neg.mul hR
  unfold logPowerTailPrimitive
  convert h using 1
  change _ = -(d / (d * t) / m) * Real.exp (-m * Real.log t) +
    (-(Real.log (d*t)/m + 1/m^2)) *
      (Real.exp (-m*Real.log t) * (-m*t⁻¹))
  field_simp [hd.ne', hm.ne', ht.ne']
  <;> ring

theorem logPowerTailIntegral (d m a b : ℝ) (hd : 0 < d) (hm : 0 < m)
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (d*t)*Real.exp (-m*Real.log t)/t) =
      logPowerTailPrimitive d m b - logPowerTailPrimitive d m a := by
  have hc : ContinuousOn
      (fun t : ℝ => Real.log (d*t)*Real.exp (-m*Real.log t)/t)
      (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have hp : 0 < t := ha.trans_le ht.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hc.intervalIntegrable
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact logPowerTailPrimitive_hasDerivAt d m t hd hm (ha.trans_le ht.1)

theorem logPowerTailPrimitive_nonpos (d m t : ℝ) (hd : 1 ≤ d) (hm : 0 < m)
    (ht : 1 ≤ t) : logPowerTailPrimitive d m t ≤ 0 := by
  have hprod : 1 ≤ d*t := by nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr ht)]
  have hlog := Real.log_nonneg hprod
  unfold logPowerTailPrimitive
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (add_nonneg (div_nonneg hlog hm.le) (div_nonneg zero_le_one (sq_nonneg m))))
    (Real.exp_pos _).le

theorem logPowerTailIntegral_bound (d m a b : ℝ) (hd : 1 ≤ d) (hm : 0 < m)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (d*t)*Real.exp (-m*Real.log t)/t) ≤
      (Real.log (d*a)/m+1/m^2)*Real.exp (-m*Real.log a) := by
  rw [logPowerTailIntegral d m a b (by linarith) hm (by linarith) hab]
  have h := logPowerTailPrimitive_nonpos d m b hd hm (ha.trans hab)
  unfold logPowerTailPrimitive
  unfold logPowerTailPrimitive at h
  linarith only [h]

theorem logPowerIntegrand_eq (d m t : ℝ) (ht : 0 < t) :
    Real.log (d*t)*Real.exp (-m*Real.log t)/t =
      Real.log (d*t)/t^(m+1) := by
  rw [Real.rpow_def_of_pos ht,
    show Real.log t*(m+1) = Real.log t + m*Real.log t by ring,
    Real.exp_add, Real.exp_log ht,
    show -m*Real.log t = -(m*Real.log t) by ring, Real.exp_neg]
  field_simp [ht.ne', (Real.exp_pos (m*Real.log t)).ne']
  <;> ring

/- Appendix A.6: endpoint certificates on a finite range.  Monotonicity
   lets two rationally certified endpoint enclosures cover the entire cell.
   No actual large-range prime-count certificate is asserted here. -/
theorem psiAP_mono (q a : ℕ) : Monotone (psiAP q a) := by
  intro n m hnm
  unfold psiAP
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hr, hmod⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by have := Finset.mem_range.mp hr; omega), hmod⟩
  · intro k hk hnot
    exact ArithmeticFunction.vonMangoldt_nonneg

theorem bmor_cell_certificate (q a A B n : ℕ) (hq : 1 ≤ q) (hA : 2 ≤ A)
    (hAn : A ≤ n) (hnB : n ≤ B)
    (hlo : (B:ℝ)/(q.totient:ℝ) - psiAP q a A ≤
      (A:ℝ)/(840*Real.log (B:ℝ)))
    (hhi : psiAP q a B - (A:ℝ)/(q.totient:ℝ) ≤
      (A:ℝ)/(840*Real.log (B:ℝ))) :
    |psiAP q a n - (n:ℝ)/(q.totient:ℝ)| ≤
      (n:ℝ)/(840*Real.log (n:ℝ)) := by
  have hA' : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hAn' : (A:ℝ) ≤ (n:ℝ) := by exact_mod_cast hAn
  have hnB' : (n:ℝ) ≤ (B:ℝ) := by exact_mod_cast hnB
  have hln : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlB : Real.log (n:ℝ) ≤ Real.log (B:ℝ) :=
    Real.log_le_log (by linarith) hnB'
  have hp := Nat.totient_pos.mpr (by omega : 0 < q)
  have hp' : (0:ℝ) < q.totient := by exact_mod_cast hp
  have hl := psiAP_mono q a hAn
  have hh := psiAP_mono q a hnB
  have hmainl := div_le_div_of_nonneg_right hAn' hp'.le
  have hmainh := div_le_div_of_nonneg_right hnB' hp'.le
  have hb : (A:ℝ)/(840*Real.log (B:ℝ)) ≤ (n:ℝ)/(840*Real.log (n:ℝ)) := by
    calc
      _ ≤ (A:ℝ)/(840*Real.log (n:ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hlB (by norm_num))
      _ ≤ _ := div_le_div_of_nonneg_right hAn' (by positivity)
  apply abs_le.mpr
  constructor <;> linarith only [hl, hh, hmainl, hmainh, hlo, hhi, hb]

/-- Use kernel-checked cells to certify every integer in a finite interval. -/
theorem bmor_finite_cover (q a L U : ℕ) (hq : 1 ≤ q) (hL : 2 ≤ L)
    (cells : Finset (ℕ×ℕ))
    (hcover : ∀ n : ℕ, L ≤ n → n ≤ U →
      ∃ p ∈ cells, p.1 ≤ n ∧ n ≤ p.2)
    (hcert : ∀ p ∈ cells, 2 ≤ p.1 ∧
      (p.2:ℝ)/(q.totient:ℝ)-psiAP q a p.1 ≤
        (p.1:ℝ)/(840*Real.log (p.2:ℝ)) ∧
      psiAP q a p.2-(p.1:ℝ)/(q.totient:ℝ) ≤
        (p.1:ℝ)/(840*Real.log (p.2:ℝ))) :
    ∀ n : ℕ, L ≤ n → n ≤ U →
      |psiAP q a n - (n:ℝ)/(q.totient:ℝ)| ≤
        (n:ℝ)/(840*Real.log (n:ℝ)) := by
  intro n hn hU
  obtain ⟨p, hp, hpn, hnp⟩ := hcover n hn hU
  obtain ⟨hA, hlo, hhi⟩ := hcert p hp
  exact bmor_cell_certificate q a p.1 p.2 n hq hA hpn hnp hlo hhi


/- Analytic bridge: the Mellin transform of the inclusive twisted
   Chebyshev sum is the negative logarithmic derivative of L.
   This section proves an identity in the half-plane of absolute
   convergence, without assuming any explicit formula. -/
open scoped Topology
open Filter MeasureTheory Asymptotics

noncomputable def twistCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)

theorem twistCoeff_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) :
    ‖twistCoeff χ k‖ ≤ ArithmeticFunction.vonMangoldt k := by
  rw [twistCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (χ.norm_le_one (k : ZMod q))

theorem twistCoeff_sum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, ‖twistCoeff χ k‖) ≤
      (Real.log 4 + 4) * (n : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k :=
      Finset.sum_le_sum (fun k _ => twistCoeff_norm_le χ k)
    _ = Chebyshev.psi (n : ℝ) := by
      simp [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc]
    _ ≤ _ := Chebyshev.psi_le_const_mul_self (by positivity)

theorem twistCoeff_sum_norm_bigO {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖twistCoeff χ k‖) =O[atTop]
      (fun n : ℕ => (n : ℝ)^(1:ℝ)) := by
  apply isBigO_of_le (Real.log 4 + 4)
  intro n
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)),
    Real.rpow_one, Real.norm_of_nonneg (by positivity : 0 ≤ (n:ℝ))]
  exact twistCoeff_sum_norm_le χ n

theorem psiTwist_eq_Icc {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    psiTwist χ n = ∑ k ∈ Finset.Icc 1 n, twistCoeff χ k := by
  classical
  unfold psiTwist
  change (∑ k ∈ Finset.range (n+1), twistCoeff χ k) = _
  symm
  apply Finset.sum_subset
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk hnot
    have hr := Finset.mem_range.mp hk
    have hz : k = 0 := by
      by_contra hn
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    subst k
    simp [twistCoeff]

theorem twistLSeries_eq_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (twistCoeff χ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

theorem psiTwist_mellin_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ), psiTwist χ ⌊t⌋₊ * (t:ℂ)^(-(s+1)) := by
  rw [← twistLSeries_eq_logDeriv χ s hs]
  have h := LSeries_eq_mul_integral' (twistCoeff χ) (by norm_num : (0:ℝ) ≤ 1)
    hs (twistCoeff_sum_norm_bigO χ)
  simpa only [← psiTwist_eq_Icc] using h

/-- The half-plane Re s ≥ 1 has no nontrivial L zeros, with the principal
    character's point s=1 excluded. This does not assert a quantitative
    zero-free strip to the left of Re s=1. -/
theorem zero_re_lt_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hz : DirichletCharacter.LFunction χ s = 0)
    (he : χ ≠ 1 ∨ s ≠ 1) : s.re < 1 := by
  by_contra! hs
  exact (χ.LFunction_ne_zero_of_one_le_re he hs) hz

/- Kernel estimates for a smoothed Perron inversion. They give uniform
   absolute decay on a vertical integration line. -/
noncomputable def perronKernel (x c t : ℝ) : ℂ :=
  (x:ℂ)^((c:ℂ)+(t:ℂ)*Complex.I) /
    (((c:ℂ)+(t:ℂ)*Complex.I)*((c:ℂ)+(t:ℂ)*Complex.I+1))

theorem perronKernel_norm (x c t : ℝ) (hx : 0 < x) :
    ‖perronKernel x c t‖ =
      x^c / (Real.sqrt (c^2+t^2) * Real.sqrt ((c+1)^2+t^2)) := by
  rw [perronKernel, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero]
  congr 1
  · rw [Complex.norm_def, Complex.norm_def]
    simp [Complex.normSq_apply]
    congr 2 <;> ring

theorem perronKernel_norm_le (x c t : ℝ) (hx : 0 < x) (ht : 0 < |t|) :
    ‖perronKernel x c t‖ ≤ x^c / t^2 := by
  rw [perronKernel_norm x c t hx]
  have h1 : |t| ≤ Real.sqrt (c^2+t^2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg c])
  have h2 : |t| ≤ Real.sqrt ((c+1)^2+t^2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (c+1)])
  have hden := mul_le_mul h1 h2 (abs_nonneg t) (Real.sqrt_nonneg _)
  rw [← sq, sq_abs] at hden
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _)
    (by positivity) hden


/- Exact smoothed Perron kernel by Mathlib's Mellin inversion.
   This avoids a new contour-integration hypothesis for the kernel itself.
   The later shift across L-function zeros still needs a residue argument. -/
noncomputable def smoothCut (u : ℝ) : ℂ :=
  (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) u -
    (Set.Ioc (0:ℝ) 1).indicator (fun v => (v:ℂ)) u

theorem smoothCut_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin smoothCut s (1/(s*(s+1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc 1 (s := s)
    (by simp only [Complex.one_re]; linarith)
  simp only [Complex.cpow_one] at h1
  have h := hasMellin_sub h0.1 h1.1
  unfold smoothCut
  rw [h0.2, h1.2] at h
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (lt_irrefl _ hs)
  have hs1 : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  convert h using 1
  field_simp [hs0, hs1]
  <;> ring

theorem smoothCut_eq_max (u : ℝ) (hu : 0 < u) :
    smoothCut u = ((max (1-u) 0 : ℝ):ℂ) := by
  unfold smoothCut
  by_cases h : u ≤ 1
  · have hm : u ∈ Set.Ioc (0:ℝ) 1 := ⟨hu,h⟩
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, max_eq_left (by linarith)]
    push_cast
    rfl
  · have hm : u ∉ Set.Ioc (0:ℝ) 1 := fun hm => h hm.2
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      max_eq_right (by linarith), Complex.ofReal_zero, sub_zero]

theorem smoothCut_continuousAt (u : ℝ) (hu : 0 < u) :
    ContinuousAt smoothCut u := by
  have hc : ContinuousAt (fun v : ℝ => ((max (1-v) 0 : ℝ):ℂ)) u := by fun_prop
  apply hc.congr
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact (smoothCut_eq_max v hv).symm

theorem smoothCut_mellin_vertical_integrable (c : ℝ) (hc : 1 ≤ c) :
    Complex.VerticalIntegrable (mellin smoothCut) c := by
  have hM (t : ℝ) : mellin smoothCut ((c:ℂ)+(t:ℂ)*Complex.I) =
      1/(((c:ℂ)+(t:ℂ)*Complex.I)*((c:ℂ)+(t:ℂ)*Complex.I+1)) :=
    (smoothCut_hasMellin _ (by
      simp [Complex.add_re, Complex.mul_re]
      linarith)).2
  unfold Complex.VerticalIntegrable
  simp_rw [hM]
  apply integrable_inv_one_add_sq.mono' (g := fun t : ℝ =>
     1/(((c:ℂ)+(t:ℂ)*Complex.I)*((c:ℂ)+(t:ℂ)*Complex.I+1)))
  · fun_prop
  · filter_upwards with t
    have h := perronKernel_norm 1 c t (by norm_num)
    simp only [perronKernel, Complex.ofReal_one, Complex.one_cpow, Real.one_rpow] at h
    rw [h]
    have hc2 : 1 ≤ c^2 := by nlinarith
    have hc3 : 1 ≤ (c+1)^2 := by nlinarith
    have h1 : Real.sqrt (1+t^2) ≤ Real.sqrt (c^2+t^2) :=
      Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (1+t^2) ≤ Real.sqrt ((c+1)^2+t^2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hm := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [← sq, Real.sq_sqrt (by positivity)] at hm
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) hm

/-- Mellin inversion gives the exact triangular cutoff, not an asymptotic
    assertion and not a conditional Perron-kernel hypothesis. -/
theorem smoothed_perron_inversion (c u : ℝ) (hc : 1 ≤ c) (hu : 0 < u) :
    mellinInv c (fun s : ℂ => 1/(s*(s+1))) u =
      ((max (1-u) 0 : ℝ):ℂ) := by
  have hM : MellinConvergent smoothCut (c:ℂ) :=
    (smoothCut_hasMellin _ (by simp; linarith)).1
  have h := mellinInv_mellin_eq c smoothCut hu hM
    (smoothCut_mellin_vertical_integrable c hc) (smoothCut_continuousAt u hu)
  rw [smoothCut_eq_max u hu] at h
  rw [← h]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [(smoothCut_hasMellin ((c:ℂ)+(t:ℂ)*Complex.I) (by
    simp [Complex.add_re, Complex.mul_re]; linarith)).2]


/- Removing the smoothing: exact discrete derivative and quantitative
   finite-difference error. No prime distribution estimate is assumed. -/
noncomputable def integratedTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), ((n:ℂ)-(k:ℂ))*twistCoeff χ k

theorem integratedTwist_succ {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    integratedTwist χ (n+1) - integratedTwist χ n = psiTwist χ n := by
  unfold integratedTwist
  rw [show n+1+1 = (n+1)+1 by rfl, Finset.sum_range_succ]
  simp only [sub_self, zero_mul, add_zero]
  rw [← Finset.sum_sub_distrib]
  unfold psiTwist
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  unfold twistCoeff
  ring

theorem integratedTwist_difference {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n h : ℕ) :
    integratedTwist χ (n+h) - integratedTwist χ n =
      (h:ℂ)*psiTwist χ n +
        ∑ k ∈ Finset.Ioc n (n+h), (((n+h:ℕ):ℂ)-(k:ℂ))*twistCoeff χ k := by
  classical
  have hsub : Finset.range (n+1) ⊆ Finset.range (n+h+1) := by
    intro k hk
    have hh := Finset.mem_range.mp hk
    exact Finset.mem_range.mpr (by omega)
  have hd : Finset.range (n+h+1) \ Finset.range (n+1) = Finset.Ioc n (n+h) := by
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]
    omega
  unfold integratedTwist
  rw [← Finset.sum_sdiff hsub, hd]
  rw [add_sub_assoc, add_comm, ← add_sub_assoc]
  have hsum : (∑ k ∈ Finset.range (n+1),
      (((n+h:ℕ):ℂ)-(k:ℂ))*twistCoeff χ k) -
      (∑ k ∈ Finset.range (n+1), ((n:ℂ)-(k:ℂ))*twistCoeff χ k) =
      (h:ℂ)*psiTwist χ n := by
    rw [← Finset.sum_sub_distrib]
    unfold psiTwist
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    unfold twistCoeff
    ring
  rw [hsum]

theorem integratedTwist_difference_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n h : ℕ) (hn : 1 ≤ n) :
    ‖integratedTwist χ (n+h) - integratedTwist χ n -
      (h:ℂ)*psiTwist χ n‖ ≤ (h:ℝ)^2*Real.log ((n+h:ℕ):ℝ) := by
  rw [integratedTwist_difference χ n h, add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc n (n+h),
        ‖(((n+h:ℕ):ℂ)-(k:ℂ))*twistCoeff χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ioc n (n+h), (h:ℝ)*Real.log ((n+h:ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkn, hkh⟩ := Finset.mem_Ioc.mp hk
      have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
      have hkn' : (n:ℝ) ≤ k := by exact_mod_cast hkn.le
      have hkh' : (k:ℝ) ≤ ((n+h:ℕ):ℝ) := by exact_mod_cast hkh
      have hlog : 0 ≤ Real.log ((n+h:ℕ):ℝ) := Real.log_nonneg (by
        exact_mod_cast (by omega : 1≤n+h))
      have hc := (twistCoeff_norm_le χ k).trans ArithmeticFunction.vonMangoldt_le_log
      have hcl := hc.trans (Real.log_le_log hk0 hkh')
      have hnorm : ‖((n+h:ℕ):ℂ)-(k:ℂ)‖ ≤ (h:ℝ) := by
        rw [← Complex.ofReal_natCast (n+h), ← Complex.ofReal_natCast k,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hkh')]
        push_cast
        linarith
      rw [norm_mul]
      exact mul_le_mul hnorm hcl (norm_nonneg _) (by positivity)
    _ = _ := by
      simp [Nat.card_Ioc, nsmul_eq_mul]
      ring

theorem unsmooth_twist_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n h : ℕ) (hn : 1 ≤ n) (hh : 0 < h)
    (δ : ℂ) (B₁ B₂ : ℝ)
    (h₁ : ‖integratedTwist χ n - δ*(n:ℂ)^2/2‖ ≤ B₁)
    (h₂ : ‖integratedTwist χ (n+h) - δ*((n+h:ℕ):ℂ)^2/2‖ ≤ B₂) :
    ‖psiTwist χ n - δ*(n:ℂ)‖ ≤
      (B₁+B₂)/(h:ℝ) + (h:ℝ)*Real.log ((n+h:ℕ):ℝ) +
        ‖δ‖*(h:ℝ)/2 := by
  have herr := integratedTwist_difference_error χ n h hn
  let A := integratedTwist χ n - δ*(n:ℂ)^2/2
  let B := integratedTwist χ (n+h) - δ*((n+h:ℕ):ℂ)^2/2
  let R := integratedTwist χ (n+h) - integratedTwist χ n - (h:ℂ)*psiTwist χ n
  have he : (h:ℂ)*(psiTwist χ n - δ*(n:ℂ)) = (B-A)-R+δ*(h:ℂ)^2/2 := by
    dsimp [A,B,R]
    push_cast
    ring
  have hA : ‖A‖ ≤ B₁ := h₁
  have hB : ‖B‖ ≤ B₂ := h₂
  have hR : ‖R‖ ≤ (h:ℝ)^2*Real.log ((n+h:ℕ):ℝ) := herr
  have hD : ‖δ*(h:ℂ)^2/2‖ = ‖δ‖*(h:ℝ)^2/2 := by
    rw [norm_div, norm_mul, norm_pow]
    norm_num
  have hh' : 0 < (h:ℝ) := by exact_mod_cast hh
  have hN : ‖(h:ℂ)*(psiTwist χ n - δ*(n:ℂ))‖ ≤
      B₁+B₂ + (h:ℝ)^2*Real.log ((n+h:ℕ):ℝ) + ‖δ‖*(h:ℝ)^2/2 := by
    rw [he]
    calc
      _ ≤ ‖(B-A)-R‖+‖δ*(h:ℂ)^2/2‖ := norm_add_le _ _
      _ ≤ (‖B-A‖+‖R‖)+‖δ*(h:ℂ)^2/2‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := by
        have hBA := norm_sub_le B A
        rw [hD]
        linarith only [hA,hB,hR,hBA]
  rw [norm_mul] at hN
  have hnC : ‖(h:ℂ)‖ = (h:ℝ) := by simp
  rw [hnC] at hN
  have hQ : ‖psiTwist χ n - δ*(n:ℂ)‖ ≤
      (B₁+B₂ + (h:ℝ)^2*Real.log ((n+h:ℕ):ℝ) + ‖δ‖*(h:ℝ)^2/2)/(h:ℝ) := by
    apply (le_div_iff₀ hh').2
    simpa [mul_comm] using hN
  calc
    _ ≤ _ := hQ
    _ = _ := by field_simp [hh'.ne']; ring

end BmorScratch
