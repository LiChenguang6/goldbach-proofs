import PEqualNP.Weyl.Linear

/-!
# Layer 3c: discrete orthogonality of the additive character

`∑_{t < M} E (t k / M)` vanishes unless `M ∣ k`, in which case it is `M`.
This is the finite (Ramanujan-sum) form of the circle method's orthogonality
relation, and the discrete counterpart of Parseval used in the Type-II layer.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

lemma E_one : E (1 : ℝ) = 1 := by
  unfold E
  rw [show (((2 * Real.pi * (1 : ℝ) : ℝ) : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_two_pi_mul_I]

lemma E_nat (n : ℕ) : E ((n : ℝ)) = 1 := by
  induction n with
  | zero => simp [E_zero]
  | succ n ih => rw [Nat.cast_succ, E_add, ih, one_mul, E_one]

lemma E_neg (x : ℝ) : E (-x) = (E x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (E_neg_mul x)

lemma E_int (k : ℤ) : E ((k : ℝ)) = 1 := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn, Int.cast_natCast]
    exact E_nat n
  · rw [hn, Int.cast_neg, Int.cast_natCast, E_neg, E_nat n, inv_one]

/-- `E α = 1` exactly at the integers. -/
lemma E_eq_one_iff {α : ℝ} : E α = 1 ↔ ∃ k : ℤ, α = (k : ℝ) := by
  constructor
  · intro hE
    have hzero : ‖E α - 1‖ = 0 := by rw [hE]; simp
    rw [norm_E_sub_one] at hzero
    have hsin : Real.sin (Real.pi * α) = 0 := by
      have habs : |Real.sin (Real.pi * α)| = 0 := by
        linarith [abs_nonneg (Real.sin (Real.pi * α))]
      exact abs_eq_zero.mp habs
    rw [Real.sin_eq_zero_iff] at hsin
    obtain ⟨k, hk⟩ := hsin
    refine ⟨k, ?_⟩
    have hp : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hcomm : Real.pi * α = Real.pi * (k : ℝ) := by
      rw [← hk]
      ring
    exact mul_left_cancel₀ hp hcomm
  · rintro ⟨k, rfl⟩
    exact E_int k

lemma E_ne_one_of_not_dvd {M : ℕ} (hM : 0 < M) {k : ℤ} (hk : ¬ (M : ℤ) ∣ k) :
    E ((k : ℝ) / (M : ℝ)) ≠ 1 := by
  intro hE
  rw [E_eq_one_iff] at hE
  obtain ⟨j, hj⟩ := hE
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have h1 : (k : ℝ) = (j : ℝ) * (M : ℝ) := by
    calc (k : ℝ) = ((k : ℝ) / (M : ℝ)) * (M : ℝ) := by field_simp
      _ = (j : ℝ) * (M : ℝ) := by rw [hj]
  have h2 : k = j * (M : ℤ) := by exact_mod_cast h1
  exact hk ⟨j, by rw [mul_comm] at h2; exact h2⟩

/-- Discrete orthogonality: the `M`-th roots of unity sum to `0` off-resonance. -/
lemma sum_E_div_eq_zero {M : ℕ} (hM : 0 < M) {k : ℤ} (hk : ¬ (M : ℤ) ∣ k) :
    ∑ t ∈ Finset.range M, E ((t : ℝ) * ((k : ℝ) / (M : ℝ))) = 0 := by
  have hω : E ((k : ℝ) / (M : ℝ)) ≠ 1 := E_ne_one_of_not_dvd hM hk
  have hsum : ∑ t ∈ Finset.range M, E ((t : ℝ) * ((k : ℝ) / (M : ℝ)))
      = ∑ t ∈ Finset.range M, (E ((k : ℝ) / (M : ℝ))) ^ t := by
    exact Finset.sum_congr rfl (fun t _ => E_nat_mul t ((k : ℝ) / (M : ℝ)))
  rw [hsum, geom_sum_eq hω M]
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hpow : (E ((k : ℝ) / (M : ℝ))) ^ M = 1 := by
    rw [← E_nat_mul M ((k : ℝ) / (M : ℝ))]
    rw [show (M : ℝ) * ((k : ℝ) / (M : ℝ)) = (k : ℝ) by field_simp]
    exact E_int k
  rw [hpow, sub_self, zero_div]

/-- Two-index orthogonality: `∑_{t<M} E (t (m-n) / M)` is `M` on resonance, `0` otherwise. -/
lemma sum_E_div_sub (M : ℕ) (hM : 0 < M) (m n : ℕ) :
    ∑ t ∈ Finset.range M, E ((t : ℝ) * (((m : ℝ) - (n : ℝ)) / (M : ℝ)))
      = if (M : ℤ) ∣ ((m : ℤ) - (n : ℤ)) then ((M : ℝ) : ℂ) else 0 := by
  by_cases hdvd : (M : ℤ) ∣ ((m : ℤ) - (n : ℤ))
  · rw [if_pos hdvd]
    obtain ⟨j, hj⟩ := hdvd
    have hMj : ((m : ℝ) - (n : ℝ)) = (M : ℝ) * (j : ℝ) := by
      have hc : ((m : ℤ) - (n : ℤ) : ℤ) = (M : ℤ) * j := hj
      have := congrArg (fun x : ℤ => (x : ℝ)) hc
      push_cast at this ⊢
      exact this
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
    have hterm : ∀ t ∈ Finset.range M, E ((t : ℝ) * (((m : ℝ) - (n : ℝ)) / (M : ℝ))) = 1 := by
      intro t _
      have hq : ((m : ℝ) - (n : ℝ)) / (M : ℝ) = (j : ℝ) := by
        rw [hMj]
        field_simp
      rw [hq]
      have : (t : ℝ) * (j : ℝ) = (((t : ℤ) * j : ℤ) : ℝ) := by push_cast; ring
      rw [this]
      exact E_int _
    calc ∑ t ∈ Finset.range M, E ((t : ℝ) * (((m : ℝ) - (n : ℝ)) / (M : ℝ)))
        = ∑ t ∈ Finset.range M, (1 : ℂ) := Finset.sum_congr rfl hterm
      _ = (M : ℂ) := by simp
      _ = ((M : ℝ) : ℂ) := by push_cast; ring
  · rw [if_neg hdvd]
    have harg : ((m : ℝ) - (n : ℝ)) / (M : ℝ)
        = ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) / (M : ℝ) := by push_cast; ring
    rw [show (∑ t ∈ Finset.range M, E ((t : ℝ) * (((m : ℝ) - (n : ℝ)) / (M : ℝ))))
        = ∑ t ∈ Finset.range M, E ((t : ℝ) * (((((m : ℤ) - (n : ℤ) : ℤ) : ℝ)) / (M : ℝ))) from by
      exact Finset.sum_congr rfl (fun t _ => by rw [harg])]
    exact sum_E_div_eq_zero hM hdvd

end

end PEqualNP.Weyl
