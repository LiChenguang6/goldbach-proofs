import Mathlib

open scoped BigOperators
open MeasureTheory

namespace GoldbachB1B1

noncomputable section

/-! Frozen definitions for the type2 b1-b1 frontier grid. -/

def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) * E ((k : ℝ) * t)

def Q (n : ℕ) : ℕ :=
  (Nat.log 2 (n + 2)) ^ 2

def Q₁ (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

def H (n : ℕ) : ℕ :=
  256 * Q₁ n * Q n

def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}

def μ (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

def U (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊

def B₁ (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

def τ₁ (n m : ℕ) : ℝ :=
  ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a),
    (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) *
      ArithmeticFunction.vonMangoldt (m / a)

def Jdeep (n : ℕ) (u v : ℕ → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (wideArcs n)ᶜ.indicator
    (fun x => S n u x * S n v x * E (-(n : ℝ) * x)) t

/-! Orthogonality layer (same shape as the low-low mode scratch). -/

def frequency (k : ℤ) : ℂ :=
  (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

def mode (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (frequency k * (t : ℂ))

theorem continuous_mode (k : ℤ) : Continuous (mode k) := by
  unfold mode
  fun_prop

theorem mode_integral (k : ℤ) :
    (∫ t in (0 : ℝ)..1, mode k t) = if k = 0 then 1 else 0 := by
  by_cases zero : k = 0
  · simp [zero, mode, frequency]
  · have kNonzero : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr zero
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have frequencyNonzero : frequency k ≠ 0 := by
      exact mul_ne_zero kNonzero (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero) Complex.I_ne_zero)
    change (∫ t in (0 : ℝ)..1, Complex.exp (frequency k * (t : ℂ))) = _
    rw [ite_eq_right zero, integral_exp_mul_complex frequencyNonzero]
    simp [frequency, Complex.exp_int_mul_two_pi_mul_I]

theorem mode_mul (j k : ℤ) (t : ℝ) : mode j t * mode k t = mode (j + k) t := by
  unfold mode frequency
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem E_mode (k : ℕ) (t : ℝ) : E ((k : ℝ) * t) = mode (k : ℤ) t := by
  unfold E mode frequency
  congr 1
  push_cast
  ring

theorem E_neg_mode (n : ℕ) (t : ℝ) : E (-(n : ℝ) * t) = mode (-(n : ℤ)) t := by
  unfold E mode frequency
  congr 1
  push_cast
  ring

theorem integral_finset_mode_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (m : ι → ℤ) :
    (∫ t in (0 : ℝ)..1, ∑ i ∈ s, c i * mode (m i) t)
      = ∑ i ∈ s, c i * (if m i = 0 then 1 else 0) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [intervalIntegral.integral_const_mul, mode_integral]
  · intro i hi
    exact (continuous_const.mul (continuous_mode (m i))).intervalIntegrable 0 1

theorem conv_integral_c (n : ℕ) (c d : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1,
      (∑ k ∈ Finset.range (n + 1), c k * mode (k : ℤ) t) *
        (∑ l ∈ Finset.range (n + 1), d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t)
      = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (if k + l = n then c k * d l else 0) := by
  have hiff : ∀ k l : ℕ, (((k : ℤ) + (l : ℤ)) + (-(n : ℤ)) = 0) ↔ (k + l = n) := by
    intro k l
    omega
  let s := Finset.range (n + 1)
  let pairTerm (k l : ℕ) (t : ℝ) : ℂ :=
    (c k * d l) * mode (((k : ℤ) + (l : ℤ)) + (-(n : ℤ))) t
  have hterm : ∀ t : ℝ,
      (∑ k ∈ s, c k * mode (k : ℤ) t) * (∑ l ∈ s, d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t
        = ∑ k ∈ s, ∑ l ∈ s, pairTerm k l t := by
    intro t
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    calc (c k * mode (k : ℤ) t) * (d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t
        = (c k * d l) * ((mode (k : ℤ) t * mode (l : ℤ) t) * mode (-(n : ℤ)) t) := by ring
      _ = (c k * d l) * (mode ((k : ℤ) + (l : ℤ)) t * mode (-(n : ℤ)) t) := by
          rw [mode_mul]
      _ = pairTerm k l t := by
          rw [mode_mul]
  calc (∫ t in (0 : ℝ)..1,
          (∑ k ∈ s, c k * mode (k : ℤ) t) *
            (∑ l ∈ s, d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t)
      = ∫ t in (0 : ℝ)..1, ∑ p ∈ s ×ˢ s, pairTerm p.1 p.2 t := by
        have hProd : ∀ t : ℝ,
            (∑ k ∈ s, c k * mode (k : ℤ) t) *
              (∑ l ∈ s, d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t
              = ∑ p ∈ s ×ˢ s, pairTerm p.1 p.2 t := by
          intro t
          rw [hterm t, ← Finset.sum_product']
        simp only [hProd]
    _ = ∑ p ∈ s ×ˢ s, (c p.1 * d p.2) *
          (if (((p.1 : ℤ) + (p.2 : ℤ)) + (-(n : ℤ)) = 0) then 1 else 0) := by
        rw [integral_finset_mode_sum]
    _ = ∑ p ∈ s ×ˢ s, (if p.1 + p.2 = n then c p.1 * d p.2 else 0) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        by_cases h : (((p.1 : ℤ) + (p.2 : ℤ)) + (-(n : ℤ)) = 0)
        · have h' : p.1 + p.2 = n := (hiff p.1 p.2).mp h
          simp [h, h']
        · have h' : ¬ (p.1 + p.2 = n) := fun hh => h ((hiff p.1 p.2).mpr hh)
          simp [h, h']
    _ = ∑ k ∈ s, ∑ l ∈ s, (if k + l = n then c k * d l else 0) := by
        exact Finset.sum_product' s s (fun k l => if k + l = n then c k * d l else 0)

theorem full_integral (n : ℕ) (u v : ℕ → ℝ) :
    (∫ t in (0 : ℝ)..1, S n u t * S n v t * E (-(n : ℝ) * t))
      = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (if k + l = n then ((u k : ℂ) * (v l : ℂ)) else 0) := by
  let c : ℕ → ℂ := fun k => (u k : ℂ)
  let d : ℕ → ℂ := fun l => (v l : ℂ)
  have hSu : ∀ t : ℝ, S n u t = ∑ k ∈ Finset.range (n + 1), c k * mode (k : ℤ) t := by
    intro t
    unfold S c
    simp only [E_mode]
  have hSv : ∀ t : ℝ, S n v t = ∑ l ∈ Finset.range (n + 1), d l * mode (l : ℤ) t := by
    intro t
    unfold S d
    simp only [E_mode]
  have hE : ∀ t : ℝ, E (-(n : ℝ) * t) = mode (-(n : ℤ)) t := fun t => E_neg_mode n t
  calc (∫ t in (0 : ℝ)..1, S n u t * S n v t * E (-(n : ℝ) * t))
      = ∫ t in (0 : ℝ)..1,
          (∑ k ∈ Finset.range (n + 1), c k * mode (k : ℤ) t) *
            (∑ l ∈ Finset.range (n + 1), d l * mode (l : ℤ) t) * mode (-(n : ℤ)) t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [hSu t, hSv t, hE t]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (if k + l = n then c k * d l else 0) :=
      conv_integral_c n c d

/-! Measurability and the wide-arc subtraction identity. -/

theorem wideArcs_measurable (n : ℕ) : MeasurableSet (wideArcs n) := by
  have hEq : wideArcs n = ⋃ (q : ℕ), ⋃ (a : ℕ),
      {t : ℝ | 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp [wideArcs, Set.mem_iUnion]
  rw [hEq]
  refine MeasurableSet.iUnion fun q => ?_
  refine MeasurableSet.iUnion fun a => ?_
  by_cases hcond : (1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q)
  · have hfun : Measurable fun t : ℝ => |t - (a : ℝ) / (q : ℝ)| := by fun_prop
    have hball : MeasurableSet {t : ℝ |
        |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} :=
      measurableSet_le hfun measurable_const
    have heq : {t : ℝ | 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} =
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      constructor
      · rintro ⟨_, _, _, _, hq⟩
        exact hq
      · intro hq
        exact ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hq⟩
    rw [heq]
    exact hball
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))} = (∅ : Set ℝ) := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3, h4, _⟩
      exact hcond ⟨h1, h2, h3, h4⟩
    rw [heq]
    exact MeasurableSet.empty

theorem jdeep_eq (n : ℕ) (u v : ℕ → ℝ) :
    Jdeep n u v =
      (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        (if k + l = n then ((u k : ℂ) * (v l : ℂ)) else 0))
      - ∫ t in (0 : ℝ)..1, (wideArcs n).indicator
          (fun x => S n u x * S n v x * E (-(n : ℝ) * x)) t := by
  let f : ℝ → ℂ := fun x => S n u x * S n v x * E (-(n : ℝ) * x)
  have hCont : Continuous f := by
    unfold f S E
    fun_prop
  have hf : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hCont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hmw : MeasurableSet (wideArcs n) := wideArcs_measurable n
  have hI : IntervalIntegrable ((wideArcs n).indicator f) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact (hCont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator hmw
  have hDec : (wideArcs n)ᶜ.indicator f = f - (wideArcs n).indicator f :=
    Set.indicator_compl (wideArcs n) f
  have hJ : Jdeep n u v = ∫ t in (0 : ℝ)..1, ((wideArcs n)ᶜ.indicator f) t := by
    rfl
  calc Jdeep n u v
      = ∫ t in (0 : ℝ)..1, ((wideArcs n)ᶜ.indicator f) t := hJ
    _ = ∫ t in (0 : ℝ)..1, (f - (wideArcs n).indicator f) t := by
        rw [hDec]
    _ = (∫ t in (0 : ℝ)..1, f t) -
          ∫ t in (0 : ℝ)..1, ((wideArcs n).indicator f) t :=
      intervalIntegral.integral_sub hf hI
    _ = (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
          (if k + l = n then ((u k : ℂ) * (v l : ℂ)) else 0)) -
        ∫ t in (0 : ℝ)..1, ((wideArcs n).indicator f) t := by
        rw [full_integral n u v]

end

end GoldbachB1B1
