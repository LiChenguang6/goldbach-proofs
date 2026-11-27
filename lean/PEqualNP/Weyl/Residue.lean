import PEqualNP.Weyl.Alpha

/-!
# Layer 6: residue orthogonality and complete blocks

The Type-II engine: for `(a, q) = 1`, the bilinear character `e(a m n / q)` has
zero mean over a complete residue system in `m` unless `q ∣ n`, in which case
the mean is `q`.  Consequently a block of `q * B` values of `m` contributes
exactly `B` times the complete sum.
-/

namespace PEqualNP.Weyl

noncomputable section

open Finset

/-- `(a/q) * (m*n)` is the linear character in `m` with frequency `a*n/q`. -/
lemma E_mul_div_mul (a n m q : ℕ) :
    E (((a : ℝ) / (q : ℝ)) * ((m : ℝ) * (n : ℝ)))
      = E ((m : ℝ) * (((a * n : ℕ) : ℝ) / (q : ℝ))) := by
  congr 1
  push_cast
  ring

/-- Complete residue sum: `(a, q) = 1` kills every `n` not divisible by `q`. -/
lemma sum_E_mul_div (q : ℕ) (hq : 0 < q) {a n : ℕ} (ha : Nat.Coprime a q) :
    ∑ m ∈ Finset.range q, E (((a : ℝ) / (q : ℝ)) * ((m : ℝ) * (n : ℝ)))
      = if q ∣ n then ((q : ℝ) : ℂ) else 0 := by
  have hstep :
      (∑ m ∈ Finset.range q, E (((a : ℝ) / (q : ℝ)) * ((m : ℝ) * (n : ℝ))))
        = ∑ m ∈ Finset.range q, E ((m : ℝ) * (((a * n : ℕ) : ℝ) / (q : ℝ))) :=
    Finset.sum_congr rfl (fun m _ => E_mul_div_mul a n m q)
  rw [hstep]
  by_cases hn : q ∣ n
  · obtain ⟨j, hj⟩ := hn
    have hnd : q ∣ n := ⟨j, hj⟩
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    have hn' : (n : ℝ) = (q : ℝ) * (j : ℝ) := by exact_mod_cast hj
    have hfr : (((a * n : ℕ) : ℝ) / (q : ℝ)) = ((a * j : ℕ) : ℝ) := by
      have han : (((a * n : ℕ) : ℝ)) = (a : ℝ) * (n : ℝ) := by push_cast; ring
      rw [han, hn']
      field_simp
      push_cast
      ring
    rw [if_pos hnd]
    have h1 : ∀ m ∈ Finset.range q,
        E ((m : ℝ) * (((a * n : ℕ) : ℝ) / (q : ℝ))) = 1 := by
      intro m _
      rw [hfr]
      rw [show (m : ℝ) * ((a * j : ℕ) : ℝ) = (((m * (a * j) : ℕ) : ℤ) : ℝ) by
        push_cast
        ring]
      exact E_int _
    rw [Finset.sum_congr rfl h1]
    simp
  · rw [if_neg hn]
    have hk : ¬ ((q : ℤ) ∣ (((a * n : ℕ) : ℤ))) := by
      rw [Int.natCast_dvd_natCast]
      exact fun h => hn (ha.symm.dvd_of_dvd_mul_left h)
    have hzero := sum_E_div_eq_zero hq hk
    rw [show (∑ m ∈ Finset.range q, E ((m : ℝ) * (((a * n : ℕ) : ℝ) / (q : ℝ))))
        = ∑ m ∈ Finset.range q,
            E ((m : ℝ) * (((((a * n : ℕ) : ℤ)) : ℝ) / (q : ℝ))) from by
      exact Finset.sum_congr rfl (fun m _ => by congr 1)]
    exact hzero

/-- Shifting a complete residue system by a multiple of `q` does not change the
value of the sum, because the shift contributes an integer phase. -/
lemma sum_E_mul_div_shift (q B : ℕ) (hq : 0 < q) (a n : ℕ) :
    (∑ r ∈ Finset.range q,
        E (((a : ℝ) / (q : ℝ)) * ((((q * B + r : ℕ) : ℝ)) * (n : ℝ))))
      = ∑ r ∈ Finset.range q, E (((a : ℝ) / (q : ℝ)) * ((r : ℝ) * (n : ℝ))) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  apply Finset.sum_congr rfl
  intro r _
  have hcast : (((q * B + r : ℕ) : ℝ)) = (q : ℝ) * (B : ℝ) + (r : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hsplit : ((a : ℝ) / (q : ℝ)) * (((q : ℝ) * (B : ℝ) + (r : ℝ)) * (n : ℝ))
      = ((a : ℝ) * (B : ℝ) * (n : ℝ)) + ((a : ℝ) / (q : ℝ)) * ((r : ℝ) * (n : ℝ)) := by
    field_simp
  rw [hsplit, E_add]
  have hint : E ((a : ℝ) * (B : ℝ) * (n : ℝ)) = 1 := by
    have hz : ((a : ℝ) * (B : ℝ) * (n : ℝ)) = (((a * B * n : ℕ) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hz]
    exact E_int _
  simp only [hint, one_mul]

/-- A block of `B` complete residue systems contributes `B` copies of the
complete sum. -/
lemma sum_E_mul_div_blocks (q B : ℕ) (hq : 0 < q) {a n : ℕ} (ha : Nat.Coprime a q) :
    ∑ m ∈ Finset.range (q * B), E (((a : ℝ) / (q : ℝ)) * ((m : ℝ) * (n : ℝ)))
      = (B : ℂ) * (if q ∣ n then ((q : ℝ) : ℂ) else 0) := by
  induction B with
  | zero => simp
  | succ B ih =>
      have hsplit : q * (B + 1) = q * B + q := Nat.mul_succ q B
      rw [hsplit, Finset.sum_range_add, ih, sum_E_mul_div_shift q B hq a n, sum_E_mul_div q hq ha]
      push_cast
      ring

end

end PEqualNP.Weyl
