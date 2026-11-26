import PEqualNP.Weyl.Ortho

/-!
# Layer 3d: periodicity of the quadratic phase modulo `q`

Writing `n = q * m + r` with `0 ≤ r < q`,

`a (q m + r)² / q = a r² / q + a m (q m + 2 r)`,

and the correction term `quadShift q m r a` is an integer.  Hence the quadratic
phase `E (a n² / q)` only depends on the residue `r = n mod q`: it is
`q`-periodic in `n`.  This is the reduction that turns the full quadratic sum
into `q` short sums, each carrying a Gauss-type factor `E (a r² / q)`.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- The integer by which the quadratic phase shifts when `n` moves from `r` to `q * m + r`. -/
def quadShift (q m r a : ℕ) : ℤ :=
  (a : ℤ) * (m : ℤ) * ((q : ℤ) * (m : ℤ) + 2 * (r : ℤ))

/-- Shifting the character by an integer does not change it. -/
lemma E_add_int {x : ℝ} (k : ℤ) : E (x + (k : ℝ)) = E x := by
  rw [E_add, E_int k, mul_one]

/-- The phase correction in the residue decomposition is an integer shift. -/
lemma quad_phase_add {q : ℕ} (hq : 0 < q) (a m r : ℕ) :
    (a : ℝ) * (((q * m + r : ℕ) : ℝ)) ^ 2 / (q : ℝ)
      = (a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ) + (quadShift q m r a : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hqr : (((q * m + r : ℕ) : ℝ)) = (q : ℝ) * (m : ℝ) + (r : ℝ) := by
    push_cast
    ring
  have hK : (quadShift q m r a : ℝ)
      = (a : ℝ) * (m : ℝ) * ((q : ℝ) * (m : ℝ) + 2 * (r : ℝ)) := by
    unfold quadShift
    push_cast
    ring
  rw [hqr, hK]
  field_simp
  ring

/-- `q`-periodicity of the quadratic phase `E (a n² / q)` in the index `n`. -/
lemma E_quad_periodic {q : ℕ} (hq : 0 < q) (a m r : ℕ) :
    E ((a : ℝ) * (((q * m + r : ℕ) : ℝ)) ^ 2 / (q : ℝ))
      = E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)) :=
  (congrArg E (quad_phase_add hq a m r)).trans (E_add_int (quadShift q m r a))

/-- The quadratic sum over the full block `n < q * M` factors through the residue
sum: each residue `r` contributes exactly `M` times its Gauss-type weight. -/
lemma sum_quad_block {q : ℕ} (hq : 0 < q) (a M : ℕ) :
    ∑ n ∈ Finset.range (q * M), E ((a : ℝ) * ((n : ℝ)) ^ 2 / (q : ℝ))
      = (M : ℂ) * ∑ r ∈ Finset.range q,
          E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsplit : q * (M + 1) = q * M + q := Nat.mul_succ q M
    rw [hsplit, Finset.sum_range_add, ih]
    have hper : (∑ r ∈ Finset.range q,
          E ((a : ℝ) * (((q * M + r : ℕ) : ℝ)) ^ 2 / (q : ℝ)))
        = ∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)) :=
      Finset.sum_congr rfl (fun r _ => E_quad_periodic hq a M r)
    rw [hper]
    push_cast
    ring

end

end PEqualNP.Weyl
